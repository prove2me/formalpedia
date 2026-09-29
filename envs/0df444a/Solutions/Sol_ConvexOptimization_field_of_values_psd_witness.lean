-- Prove2me | solution 1 for ConvexOptimization.field_of_values_psd_witness
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-16T03:22:20.44109+00:00
-- url     : https://prove2.me/submissions/5696acb3-b304-4047-a2ce-4001d527cef5

import Mathlib
open scoped RealInnerProductSpace ENNReal
open MeasureTheory
namespace ConvexOptimization

lemma sum_matrix_apply {n k : Type*} [Fintype k] (f : k → Matrix n n ℝ) (i j : n) :
    (∑ x, f x) i j = ∑ x, f x i j := by
  classical
  have hs : ∀ s : Finset k, (∑ x ∈ s, f x) i j = ∑ x ∈ s, f x i j := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert x s hx ih => simp [hx, ih, Matrix.add_apply]
  simpa using hs Finset.univ

lemma quad_eq_trace_mul_vecMulVec {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ A.mulVec x = (A * Matrix.vecMulVec x x).trace := by
  classical
  simp only [dotProduct, Matrix.mulVec, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.vecMulVec_apply]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma trace_mul_sum_vecMulVec {n k : Type*} [Fintype n] [Fintype k]
    (A : Matrix n n ℝ) (v : k → n → ℝ) :
    (A * ∑ i, Matrix.vecMulVec (v i) (v i)).trace =
      ∑ i, v i ⬝ᵥ A.mulVec (v i) := by
  classical
  rw [Matrix.mul_sum]
  calc
    (∑ i, A * Matrix.vecMulVec (v i) (v i)).trace =
        ∑ i, (A * Matrix.vecMulVec (v i) (v i)).trace := by
          simpa using map_sum (Matrix.traceLinearMap n ℝ ℝ)
            (fun i => A * Matrix.vecMulVec (v i) (v i)) Finset.univ
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (quad_eq_trace_mul_vecMulVec A (v i)).symm

noncomputable def psdSpectralVecs {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℝ} (hX : X.PosSemidef) (i : n) : n → ℝ :=
  Real.sqrt (hX.isHermitian.eigenvalues i) •
    Matrix.col (hX.isHermitian.eigenvectorUnitary : Matrix n n ℝ) i

lemma psd_eq_sum_vecMulVec {n : Type*} [Fintype n] [DecidableEq n]
    {X : Matrix n n ℝ} (hX : X.PosSemidef) :
    X = ∑ i, Matrix.vecMulVec (psdSpectralVecs hX i) (psdSpectralVecs hX i) := by
  calc
    X = Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hX.isHermitian.eigenvectorUnitary
        (Matrix.diagonal (RCLike.ofReal ∘ hX.isHermitian.eigenvalues)) :=
      hX.isHermitian.spectral_theorem
    _ = ∑ i, Matrix.vecMulVec (psdSpectralVecs hX i) (psdSpectralVecs hX i) := by
      ext i j
      rw [sum_matrix_apply]
      simp [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal,
        psdSpectralVecs]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Matrix.vecMulVec_apply]
      rw [← mul_assoc, Real.mul_self_sqrt (hX.eigenvalues_nonneg x)]
      ring


lemma hermitian_apply_eq_sum_eigen {n : Type*} [Fintype n] [DecidableEq n]
    {K : Matrix n n ℝ} (hK : K.IsHermitian) (i j : n) :
    K i j = ∑ k, (hK.eigenvectorUnitary : Matrix n n ℝ) i k *
      hK.eigenvalues k * (hK.eigenvectorUnitary : Matrix n n ℝ) j k := by
  calc
    K i j = (Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hK.eigenvectorUnitary
        (Matrix.diagonal (RCLike.ofReal ∘ hK.eigenvalues))) i j :=
      congr_fun (congr_fun hK.spectral_theorem i) j
    _ = _ := by
      simp [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal]

lemma unitary_cols_sum {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℝ) (i j : n) :
    ∑ k, (U : Matrix n n ℝ) i k * (U : Matrix n n ℝ) j k = (1 : Matrix n n ℝ) i j := by
  have h := congr_fun (congr_fun (Unitary.coe_mul_star_self U) i) j
  simpa [Matrix.mul_apply] using h

lemma dominant_eigen_boundary_zero {K : Matrix (Fin 2) (Fin 2) ℝ}
    (hK : K.IsHermitian) (hK0 : K ≠ 0)
    (hdom : |hK.eigenvalues 1| ≤ |hK.eigenvalues 0|) :
    ∃ (t : ℝ) (w : Fin 2 → ℝ),
      (1 : Matrix (Fin 2) (Fin 2) ℝ) + t • K = Matrix.vecMulVec w w := by
  let l0 := hK.eigenvalues 0
  let l1 := hK.eigenvalues 1
  have hl0 : l0 ≠ 0 := by
    intro hz
    have ha : |l1| ≤ 0 := by simpa [l0, hz] using hdom
    have hl1 : l1 = 0 := abs_eq_zero.mp (le_antisymm ha (abs_nonneg _))
    have he : hK.eigenvalues = 0 := by
      funext i
      fin_cases i <;> simp [l0, l1, hz, hl1]
    exact hK0 (hK.eigenvalues_eq_zero_iff.mp he)
  have hr : 0 ≤ 1 - l1 / l0 := by
    have hb := abs_le.mp hdom
    rcases lt_or_gt_of_ne hl0 with hn | hp
    · have hle : l0 ≤ l1 := by simpa [l0, l1, abs_of_neg hn] using hb.1
      exact sub_nonneg.mpr ((div_le_iff_of_neg hn).2 (by simpa using hle))
    · have hle : l1 ≤ l0 := by simpa [l0, l1, abs_of_pos hp] using hb.2
      exact sub_nonneg.mpr ((div_le_one hp).2 hle)
  let U : Matrix (Fin 2) (Fin 2) ℝ := hK.eigenvectorUnitary
  let r : ℝ := 1 - l1 / l0
  refine ⟨-l0⁻¹, Real.sqrt r • Matrix.col U 1, ?_⟩
  ext i j
  have hk := hermitian_apply_eq_sum_eigen hK i j
  rw [Fin.sum_univ_two] at hk
  have hu := unitary_cols_sum hK.eigenvectorUnitary i j
  rw [Fin.sum_univ_two] at hu
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.col_apply]
  have hsqrt : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt (by simpa [r] using hr)
  have hw : Real.sqrt r * U i 1 * (Real.sqrt r * U j 1) = r * U i 1 * U j 1 := by
    rw [show Real.sqrt r * U i 1 * (Real.sqrt r * U j 1) =
      (Real.sqrt r * Real.sqrt r) * U i 1 * U j 1 by ring, hsqrt]
  rw [hw]
  dsimp [U, r, l0, l1]
  dsimp [l0, l1] at hl0
  rw [hk, ← hu]
  simp only [Matrix.IsHermitian.eigenvectorUnitary_apply]
  field_simp
  ring


lemma dominant_eigen_boundary_one {K : Matrix (Fin 2) (Fin 2) ℝ}
    (hK : K.IsHermitian) (hK0 : K ≠ 0)
    (hdom : |hK.eigenvalues 0| ≤ |hK.eigenvalues 1|) :
    ∃ (t : ℝ) (w : Fin 2 → ℝ),
      (1 : Matrix (Fin 2) (Fin 2) ℝ) + t • K = Matrix.vecMulVec w w := by
  let l0 := hK.eigenvalues 0
  let l1 := hK.eigenvalues 1
  have hl1 : l1 ≠ 0 := by
    intro hz
    have ha : |l0| ≤ 0 := by simpa [l1, hz] using hdom
    have hl0 : l0 = 0 := abs_eq_zero.mp (le_antisymm ha (abs_nonneg _))
    have he : hK.eigenvalues = 0 := by
      funext i
      fin_cases i <;> simp [l0, l1, hz, hl0]
    exact hK0 (hK.eigenvalues_eq_zero_iff.mp he)
  have hr : 0 ≤ 1 - l0 / l1 := by
    have hb := abs_le.mp hdom
    rcases lt_or_gt_of_ne hl1 with hn | hp
    · have hle : l1 ≤ l0 := by simpa [l0, l1, abs_of_neg hn] using hb.1
      exact sub_nonneg.mpr ((div_le_iff_of_neg hn).2 (by simpa using hle))
    · have hle : l0 ≤ l1 := by simpa [l0, l1, abs_of_pos hp] using hb.2
      exact sub_nonneg.mpr ((div_le_one hp).2 hle)
  let U : Matrix (Fin 2) (Fin 2) ℝ := hK.eigenvectorUnitary
  let r : ℝ := 1 - l0 / l1
  refine ⟨-l1⁻¹, Real.sqrt r • Matrix.col U 0, ?_⟩
  ext i j
  have hk := hermitian_apply_eq_sum_eigen hK i j
  rw [Fin.sum_univ_two] at hk
  have hu := unitary_cols_sum hK.eigenvectorUnitary i j
  rw [Fin.sum_univ_two] at hu
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.col_apply]
  have hsqrt : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt (by simpa [r] using hr)
  have hw : Real.sqrt r * U i 0 * (Real.sqrt r * U j 0) = r * U i 0 * U j 0 := by
    rw [show Real.sqrt r * U i 0 * (Real.sqrt r * U j 0) =
      (Real.sqrt r * Real.sqrt r) * U i 0 * U j 0 by ring, hsqrt]
  rw [hw]
  dsimp [U, r, l0, l1]
  dsimp [l0, l1] at hl1
  rw [hk, ← hu]
  simp only [Matrix.IsHermitian.eigenvectorUnitary_apply]
  field_simp
  ring

lemma hermitian_two_boundary_rank_one {K : Matrix (Fin 2) (Fin 2) ℝ}
    (hK : K.IsHermitian) (hK0 : K ≠ 0) :
    ∃ (t : ℝ) (w : Fin 2 → ℝ),
      (1 : Matrix (Fin 2) (Fin 2) ℝ) + t • K = Matrix.vecMulVec w w := by
  rcases le_total |hK.eigenvalues 0| |hK.eigenvalues 1| with h | h
  · exact dominant_eigen_boundary_one hK hK0 h
  · exact dominant_eigen_boundary_zero hK hK0 h


lemma exists_nonzero_hermitian_trace_orthogonal
    (M N : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.IsHermitian) (hN : N.IsHermitian) :
    ∃ K : Matrix (Fin 2) (Fin 2) ℝ,
      K.IsHermitian ∧ K ≠ 0 ∧ (M * K).trace = 0 ∧ (N * K).trace = 0 := by
  have hm10 : M 1 0 = M 0 1 := by
    have h := congr_fun (congr_fun hM 0) 1
    simpa [Matrix.conjTranspose_apply] using h
  have hn10 : N 1 0 = N 0 1 := by
    have h := congr_fun (congr_fun hN 0) 1
    simpa [Matrix.conjTranspose_apply] using h
  let L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
    { toFun := fun z i =>
        ![M 0 0 * z 0 + 2 * M 0 1 * z 1 + M 1 1 * z 2,
          N 0 0 * z 0 + 2 * N 0 1 * z 1 + N 1 1 * z 2] i
      map_add' := by
        intro x y
        funext i
        fin_cases i <;> simp <;> ring
      map_smul' := by
        intro c x
        funext i
        fin_cases i <;> simp <;> ring }
  have hdim : Module.finrank ℝ (Fin 2 → ℝ) < Module.finrank ℝ (Fin 3 → ℝ) := by simp
  obtain ⟨z, hzker, hz0⟩ :=
    (L.ker).exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hdim)
  let K : Matrix (Fin 2) (Fin 2) ℝ := !![z 0, z 1; z 1, z 2]
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [K, Matrix.conjTranspose_apply]
  · intro hK
    apply hz0
    funext i
    fin_cases i
    · have := congr_fun (congr_fun hK 0) 0
      simpa [K] using this
    · have := congr_fun (congr_fun hK 0) 1
      simpa [K] using this
    · have := congr_fun (congr_fun hK 1) 1
      simpa [K] using this
  · have h0 := congr_fun hzker 0
    simp only [LinearMap.mem_ker] at hzker
    change L z = 0 at hzker
    have h0 := congr_fun hzker 0
    simp only [Pi.zero_apply] at h0
    simp only [K, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hm10]
    convert h0 using 1 <;> simp [L] <;> ring
  · simp only [LinearMap.mem_ker] at hzker
    have h1 := congr_fun hzker 1
    simp only [Pi.zero_apply] at h1
    simp only [K, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hn10]
    convert h1 using 1 <;> simp [L] <;> ring



lemma two_by_two_trace_witness
    (M N : Matrix (Fin 2) (Fin 2) ℝ) (hM : M.IsHermitian) (hN : N.IsHermitian) :
    ∃ w : Fin 2 → ℝ,
      w ⬝ᵥ M.mulVec w = M.trace ∧ w ⬝ᵥ N.mulVec w = N.trace := by
  obtain ⟨K, hK, hK0, hMK, hNK⟩ := exists_nonzero_hermitian_trace_orthogonal M N hM hN
  obtain ⟨t, w, htw⟩ := hermitian_two_boundary_rank_one hK hK0
  refine ⟨w, ?_, ?_⟩
  · rw [quad_eq_trace_mul_vecMulVec, ← htw, Matrix.mul_add, Matrix.mul_smul]
    rw [Matrix.trace_add, Matrix.trace_smul, hMK]
    simp
  · rw [quad_eq_trace_mul_vecMulVec, ← htw, Matrix.mul_add, Matrix.mul_smul]
    rw [Matrix.trace_add, Matrix.trace_smul, hNK]
    simp


noncomputable def quadraticGramTwo {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (u v : n → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![u ⬝ᵥ A.mulVec u, u ⬝ᵥ A.mulVec v;
     v ⬝ᵥ A.mulVec u, v ⬝ᵥ A.mulVec v]

lemma quadraticGramTwo_isHermitian {n : Type*} [Fintype n]
    {A : Matrix n n ℝ} (hA : A.IsSymm) (u v : n → ℝ) :
    (quadraticGramTwo A u v).IsHermitian := by
  have hc : u ⬝ᵥ A.mulVec v = v ⬝ᵥ A.mulVec u := by
    calc
      u ⬝ᵥ A.mulVec v = Matrix.vecMul u A ⬝ᵥ v := Matrix.dotProduct_mulVec u A v
      _ = A.transpose.mulVec u ⬝ᵥ v := by
        rw [show Matrix.vecMul u A = A.transpose.mulVec u by
          simpa using Matrix.vecMul_transpose A.transpose u]
      _ = A.mulVec u ⬝ᵥ v := by rw [hA]
      _ = v ⬝ᵥ A.mulVec u := dotProduct_comm _ _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quadraticGramTwo, Matrix.conjTranspose_apply, hc]

lemma quadratic_combination_eq_gram {n : Type*} [Fintype n]
    {A : Matrix n n ℝ} (hA : A.IsSymm) (u v : n → ℝ) (c : Fin 2 → ℝ) :
    (c 0 • u + c 1 • v) ⬝ᵥ A.mulVec (c 0 • u + c 1 • v) =
      c ⬝ᵥ (quadraticGramTwo A u v).mulVec c := by
  have hc : u ⬝ᵥ A.mulVec v = v ⬝ᵥ A.mulVec u := by
    calc
      u ⬝ᵥ A.mulVec v = Matrix.vecMul u A ⬝ᵥ v := Matrix.dotProduct_mulVec u A v
      _ = A.transpose.mulVec u ⬝ᵥ v := by
        rw [show Matrix.vecMul u A = A.transpose.mulVec u by
          simpa using Matrix.vecMul_transpose A.transpose u]
      _ = A.mulVec u ⬝ᵥ v := by rw [hA]
      _ = v ⬝ᵥ A.mulVec u := dotProduct_comm _ _
  have hgram : c ⬝ᵥ (quadraticGramTwo A u v).mulVec c =
      c 0 * ((u ⬝ᵥ A.mulVec u) * c 0 + (u ⬝ᵥ A.mulVec v) * c 1) +
      c 1 * ((v ⬝ᵥ A.mulVec u) * c 0 + (v ⬝ᵥ A.mulVec v) * c 1) := by
    simp [quadraticGramTwo, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hgram]
  simp_rw [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [hc]
  ring

lemma quadraticGramTwo_trace {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) (u v : n → ℝ) :
    (quadraticGramTwo A u v).trace = u ⬝ᵥ A.mulVec u + v ⬝ᵥ A.mulVec v := by
  simp [quadraticGramTwo, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

lemma quadratic_pair_compress {n : Type*} [Fintype n]
    (A B : Matrix n n ℝ) (hA : A.IsSymm) (hB : B.IsSymm) (u v : n → ℝ) :
    ∃ x : n → ℝ,
      x ⬝ᵥ A.mulVec x = u ⬝ᵥ A.mulVec u + v ⬝ᵥ A.mulVec v ∧
      x ⬝ᵥ B.mulVec x = u ⬝ᵥ B.mulVec u + v ⬝ᵥ B.mulVec v := by
  obtain ⟨c, hcA, hcB⟩ := two_by_two_trace_witness
    (quadraticGramTwo A u v) (quadraticGramTwo B u v)
    (quadraticGramTwo_isHermitian hA u v) (quadraticGramTwo_isHermitian hB u v)
  refine ⟨c 0 • u + c 1 • v, ?_, ?_⟩
  · rw [quadratic_combination_eq_gram hA, hcA, quadraticGramTwo_trace]
  · rw [quadratic_combination_eq_gram hB, hcB, quadraticGramTwo_trace]


lemma quadratic_finset_compress {n k : Type*} [Fintype n]
    (A B : Matrix n n ℝ) (hA : A.IsSymm) (hB : B.IsSymm)
    (v : k → n → ℝ) (s : Finset k) :
    ∃ x : n → ℝ,
      x ⬝ᵥ A.mulVec x = ∑ i ∈ s, v i ⬝ᵥ A.mulVec (v i) ∧
      x ⬝ᵥ B.mulVec x = ∑ i ∈ s, v i ⬝ᵥ B.mulVec (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_, ?_⟩ <;> simp
  | @insert i s hi ih =>
      obtain ⟨y, hyA, hyB⟩ := ih
      obtain ⟨x, hxA, hxB⟩ := quadratic_pair_compress A B hA hB (v i) y
      refine ⟨x, ?_, ?_⟩
      · rw [hxA, hyA, Finset.sum_insert hi]
      · rw [hxB, hyB, Finset.sum_insert hi]

lemma quadratic_fintype_compress {n k : Type*} [Fintype n] [Fintype k]
    (A B : Matrix n n ℝ) (hA : A.IsSymm) (hB : B.IsSymm) (v : k → n → ℝ) :
    ∃ x : n → ℝ,
      x ⬝ᵥ A.mulVec x = ∑ i, v i ⬝ᵥ A.mulVec (v i) ∧
      x ⬝ᵥ B.mulVec x = ∑ i, v i ⬝ᵥ B.mulVec (v i) := by
  simpa using quadratic_finset_compress A B hA hB v Finset.univ


end ConvexOptimization


theorem solution {nn : ℕ}
    (A B : Matrix (Fin nn) (Fin nn) ℝ) (hA : A.IsSymm) (hB : B.IsSymm)
    (X : Matrix (Fin nn) (Fin nn) ℝ) (hX : X.PosSemidef) :
    ∃ x : Fin nn → ℝ,
      x ⬝ᵥ A.mulVec x = (A * X).trace ∧ x ⬝ᵥ B.mulVec x = (B * X).trace := by
  let v : Fin nn → Fin nn → ℝ := fun i => ConvexOptimization.psdSpectralVecs hX i
  obtain ⟨x, hxA, hxB⟩ := ConvexOptimization.quadratic_fintype_compress A B hA hB v
  refine ⟨x, ?_, ?_⟩
  · rw [hxA, ← ConvexOptimization.trace_mul_sum_vecMulVec]
    congr 2
    exact (ConvexOptimization.psd_eq_sum_vecMulVec hX).symm
  · rw [hxB, ← ConvexOptimization.trace_mul_sum_vecMulVec]
    congr 2
    exact (ConvexOptimization.psd_eq_sum_vecMulVec hX).symm
