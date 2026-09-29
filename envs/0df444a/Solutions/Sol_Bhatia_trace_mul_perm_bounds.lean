-- Prove2me | solution 1 for Bhatia.trace_mul_perm_bounds
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-14T01:04:49.152294+00:00
-- url     : https://prove2.me/submissions/ca10a731-5fb1-4812-82ac-46e780c6d8d4

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.InnerProductSpace.PiL2

open Matrix Finset Unitary


open Matrix Finset

/-- The Gram matrix of squared inner products of two orthonormal bases is doubly stochastic. -/
theorem doublyStochastic_inner_sq {n : ℕ}
    (e f : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    (Matrix.of fun i j => (inner ℝ (e i) (f j) : ℝ) ^ 2) ∈ doublyStochastic ℝ (Fin n) := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => sq_nonneg _, fun i => ?_, fun j => ?_⟩
  · have h := f.sum_inner_mul_inner (e i) (e i)
    have hnorm : (inner ℝ (e i) (e i) : ℝ) = 1 := by
      rw [real_inner_self_eq_norm_sq, e.orthonormal.1 i]; norm_num
    rw [hnorm] at h
    simp only [Matrix.of_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => by rw [real_inner_comm (f j) (e i)]; ring
  · have h := e.sum_inner_mul_inner (f j) (f j)
    have hnorm : (inner ℝ (f j) (f j) : ℝ) = 1 := by
      rw [real_inner_self_eq_norm_sq, f.orthonormal.1 j]; norm_num
    rw [hnorm] at h
    simp only [Matrix.of_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm (f j) (e i)]; ring

/-- Consequence: the pairing decomposes as a convex combination over permutations,
which is exactly the shape Birkhoff + the rearrangement inequality consume. -/
theorem exists_perm_weights_inner_sq {n : ℕ}
    (e f : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    ∃ w : Equiv.Perm (Fin n) → ℝ, (∀ σ, 0 ≤ w σ) ∧ ∑ σ, w σ = 1 ∧
      ∀ i j, (∑ σ, w σ • (σ.permMatrix ℝ)) i j = (inner ℝ (e i) (f j) : ℝ) ^ 2 := by
  obtain ⟨w, hw0, hw1, hw2⟩ :=
    exists_eq_sum_perm_of_mem_doublyStochastic (doublyStochastic_inner_sq e f)
  exact ⟨w, hw0, hw1, fun i j => by rw [hw2]; rfl⟩



namespace BhatiaStep2

variable {n : ℕ}

/-- The trace form of a diagonal-conjugated product: `tr(Dλ M Dμ Mᵀ) = ∑ᵢⱼ λᵢ μⱼ Mᵢⱼ²`. -/
theorem trace_diagonal_mul_mul_diagonal_mul_transpose
    (lam mu : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (Matrix.diagonal lam * M * Matrix.diagonal mu * Mᵀ).trace
      = ∑ i, ∑ j, lam i * mu j * M i j ^ 2 := by
  simp only [Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun j _ => by ring

end BhatiaStep2

open BhatiaStep2


namespace BhatiaAssembly

variable {n : ℕ}

lemma conjT_real (A : Matrix (Fin n) (Fin n) ℝ) : Aᴴ = Aᵀ := by
  ext i j; simp [Matrix.conjTranspose_apply]

/-- The spectral theorem in plain `V * diagonal λ * Vᵀ` form over `ℝ`. -/
lemma spectral_real {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
        * Matrix.diagonal hA.eigenvalues
        * (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
  have h := hA.spectral_theorem
  rw [conjStarAlgAut_apply] at h
  rw [← conjT_real, ← Matrix.star_eq_conjTranspose]
  exact h

/-- The entries of `Vᵀ W` are the inner products of the two eigenbases. -/
lemma vT_mul_w_apply {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (i j : Fin n) :
    ((hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᵀ
        * (hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) i j
      = (inner ℝ (hA.eigenvectorBasis i) (hB.eigenvectorBasis j) : ℝ) := by
  rw [Matrix.mul_apply]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.transpose_apply, Matrix.IsHermitian.eigenvectorUnitary_apply,
    dotProduct, Pi.star_apply, star_trivial, WithLp.ofLp_toLp]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **Spectral expansion of the Frobenius pairing** (steps 2 and 5 of the roadmap).
For two real symmetric matrices the pairing expands over both eigenbases, with the
squared inner products of the eigenvectors as coefficients. Combined with
`doublyStochastic_inner_sq` (step 3) those coefficients form a doubly stochastic matrix,
so Birkhoff (step 4) exhibits the pairing as a convex combination of the permutation sums
`∑ᵢ λᵢ(A) λ_{σ(i)}(B)`; the rearrangement inequality (step 6) then gives Bhatia's bounds. -/
theorem trace_mul_eq_sum_eigen (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B).trace
      = ∑ i, ∑ j, hA.eigenvalues i * hB.eigenvalues j
          * (inner ℝ (hA.eigenvectorBasis i) (hB.eigenvectorBasis j) : ℝ) ^ 2 := by
  classical
  set V : Matrix (Fin n) (Fin n) ℝ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hV
  set W : Matrix (Fin n) (Fin n) ℝ := (hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hW
  have hMt : (Vᵀ * W)ᵀ = Wᵀ * V := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have htr : (A * B).trace
      = (Matrix.diagonal hA.eigenvalues * (Vᵀ * W) * Matrix.diagonal hB.eigenvalues
          * (Vᵀ * W)ᵀ).trace := by
    rw [hMt]
    conv_lhs => rw [spectral_real hA, spectral_real hB]
    rw [show (V * Matrix.diagonal hA.eigenvalues * Vᵀ)
          * (W * Matrix.diagonal hB.eigenvalues * Wᵀ)
        = V * (Matrix.diagonal hA.eigenvalues * (Vᵀ * W) * Matrix.diagonal hB.eigenvalues * Wᵀ)
        from by simp [Matrix.mul_assoc], Matrix.trace_mul_comm]
    congr 1
    simp [Matrix.mul_assoc]
  rw [htr, trace_diagonal_mul_mul_diagonal_mul_transpose]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [vT_mul_w_apply hA hB i j]

/-- **The convex-combination form** (steps 3, 4 and the assembly). The Frobenius pairing of
two real symmetric matrices is a convex combination of the permutation sums
`∑ᵢ λᵢ(A) λ_{σ(i)}(B)`. Both halves of Bhatia's inequality follow by the rearrangement
inequality applied to each permutation sum. -/
theorem trace_mul_eq_convex_comb_perm (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∃ w : Equiv.Perm (Fin n) → ℝ, (∀ σ, 0 ≤ w σ) ∧ ∑ σ, w σ = 1 ∧
      (A * B).trace = ∑ σ, w σ * ∑ i, hA.eigenvalues i * hB.eigenvalues (σ i) := by
  classical
  obtain ⟨w, hw0, hw1, hw2⟩ :=
    exists_eq_sum_perm_of_mem_doublyStochastic
      (doublyStochastic_inner_sq hA.eigenvectorBasis hB.eigenvectorBasis)
  refine ⟨w, hw0, hw1, ?_⟩
  -- The coefficient matrix, applied to the eigenvalues of `B`.
  have key : ∀ i, ∑ j, (inner ℝ (hA.eigenvectorBasis i) (hB.eigenvectorBasis j) : ℝ) ^ 2
        * hB.eigenvalues j
      = ∑ σ : Equiv.Perm (Fin n), w σ * hB.eigenvalues (σ i) := by
    intro i
    have h1 : (Matrix.of fun i j =>
        (inner ℝ (hA.eigenvectorBasis i) (hB.eigenvectorBasis j) : ℝ) ^ 2)
          *ᵥ hB.eigenvalues
        = (∑ σ : Equiv.Perm (Fin n), w σ • σ.permMatrix ℝ) *ᵥ hB.eigenvalues := by
      rw [hw2]
    have h2 := congrFun h1 i
    rw [Matrix.sum_mulVec] at h2
    simpa [Matrix.mulVec, dotProduct, Finset.sum_apply, Matrix.smul_mulVec,
      permMatrix_mulVec] using h2
  rw [trace_mul_eq_sum_eigen A B hA hB]
  calc ∑ i, ∑ j, hA.eigenvalues i * hB.eigenvalues j
          * (inner ℝ (hA.eigenvectorBasis i) (hB.eigenvectorBasis j) : ℝ) ^ 2
      = ∑ i, hA.eigenvalues i
          * ∑ j, (inner ℝ (hA.eigenvectorBasis i) (hB.eigenvectorBasis j) : ℝ) ^ 2
              * hB.eigenvalues j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ i, ∑ σ : Equiv.Perm (Fin n), w σ * (hA.eigenvalues i * hB.eigenvalues (σ i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [key i, Finset.mul_sum]
        exact Finset.sum_congr rfl fun σ _ => by ring
    _ = ∑ σ : Equiv.Perm (Fin n), w σ * ∑ i, hA.eigenvalues i * hB.eigenvalues (σ i) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun σ _ => (Finset.mul_sum _ _ _).symm

/-- **Bhatia's inequality, lower half.** Some permutation pairing of the eigenvalues
underestimates the pairing. With the rearrangement inequality this is the reverse-ordered
sum `∑ᵢ λᵢ(A) λ_{n+1−i}(B)`. -/
theorem exists_perm_sum_le_trace_mul (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∃ σ : Equiv.Perm (Fin n),
      ∑ i, hA.eigenvalues i * hB.eigenvalues (σ i) ≤ (A * B).trace := by
  classical
  obtain ⟨w, hw0, hw1, hw2⟩ := trace_mul_eq_convex_comb_perm A B hA hB
  obtain ⟨σ₀, -, hσ₀⟩ := Finset.exists_min_image (Finset.univ : Finset (Equiv.Perm (Fin n)))
    (fun σ => ∑ i, hA.eigenvalues i * hB.eigenvalues (σ i)) ⟨1, Finset.mem_univ 1⟩
  refine ⟨σ₀, ?_⟩
  rw [hw2]
  calc ∑ i, hA.eigenvalues i * hB.eigenvalues (σ₀ i)
      = (∑ σ : Equiv.Perm (Fin n), w σ) * ∑ i, hA.eigenvalues i * hB.eigenvalues (σ₀ i) := by
        rw [hw1]; ring
    _ = ∑ σ : Equiv.Perm (Fin n), w σ * ∑ i, hA.eigenvalues i * hB.eigenvalues (σ₀ i) := by
        rw [Finset.sum_mul]
    _ ≤ ∑ σ : Equiv.Perm (Fin n), w σ * ∑ i, hA.eigenvalues i * hB.eigenvalues (σ i) :=
        Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_left (hσ₀ σ (Finset.mem_univ σ)) (hw0 σ)

/-- **Bhatia's inequality, upper half.** -/
theorem exists_trace_mul_le_perm_sum (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∃ σ : Equiv.Perm (Fin n),
      (A * B).trace ≤ ∑ i, hA.eigenvalues i * hB.eigenvalues (σ i) := by
  classical
  obtain ⟨w, hw0, hw1, hw2⟩ := trace_mul_eq_convex_comb_perm A B hA hB
  obtain ⟨σ₀, -, hσ₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Equiv.Perm (Fin n)))
    (fun σ => ∑ i, hA.eigenvalues i * hB.eigenvalues (σ i)) ⟨1, Finset.mem_univ 1⟩
  refine ⟨σ₀, ?_⟩
  rw [hw2]
  calc ∑ σ : Equiv.Perm (Fin n), w σ * ∑ i, hA.eigenvalues i * hB.eigenvalues (σ i)
      ≤ ∑ σ : Equiv.Perm (Fin n), w σ * ∑ i, hA.eigenvalues i * hB.eigenvalues (σ₀ i) :=
        Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_left (hσ₀ σ (Finset.mem_univ σ)) (hw0 σ)
    _ = (∑ σ : Equiv.Perm (Fin n), w σ) * ∑ i, hA.eigenvalues i * hB.eigenvalues (σ₀ i) := by
        rw [Finset.sum_mul]
    _ = ∑ i, hA.eigenvalues i * hB.eigenvalues (σ₀ i) := by rw [hw1]; ring

end BhatiaAssembly


theorem solution {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∃ σ : Equiv.Perm (Fin n),
        ∑ i, hA.eigenvalues i * hB.eigenvalues (σ i) ≤ (A * B).trace) ∧
      (∃ σ : Equiv.Perm (Fin n),
        (A * B).trace ≤ ∑ i, hA.eigenvalues i * hB.eigenvalues (σ i)) :=
  ⟨BhatiaAssembly.exists_perm_sum_le_trace_mul A B hA hB,
   BhatiaAssembly.exists_trace_mul_le_perm_sum A B hA hB⟩
