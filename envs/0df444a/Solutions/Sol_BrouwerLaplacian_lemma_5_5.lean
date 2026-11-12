-- Prove2me | solution 1 for BrouwerLaplacian.lemma_5_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:42:46.72512+00:00
-- url     : https://prove2.me/submissions/75c76013-6c0c-4cb9-bd0e-bf86b7ac80a1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BrouwerLaplacian_IsOrthProj
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2
import Definitions.Def_BrouwerLaplacian_centering
import Definitions.Def_BrouwerLaplacian_routingM
import Definitions.Def_WainwrightHDS_NucNorm_nucNorm
import Definitions.Def_BrouwerLaplacian_IsSplitWith
import Definitions.Def_BrouwerLaplacian_splitGraphOf
import Theorems.Thm_BrouwerLaplacian_lemma_3_2
import Theorems.Thm_BrouwerLaplacian_eq_5_3
import Theorems.Thm_BrouwerLaplacian_proof_lemma_5_5_N

section
namespace BrouwerLaplacian.Dev.Common

open Matrix

end BrouwerLaplacian.Dev.Common
end

section
namespace BrouwerLaplacian.Dev.L52

open Finset Matrix

theorem symm_of {n k : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : BrouwerLaplacian.IsOrthProj P k)
    (i j : Fin n) : P j i = P i j := by
  have := hP.1.apply i j
  simpa using this

end BrouwerLaplacian.Dev.L52

namespace BrouwerLaplacian
open Finset Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.OpN

open Matrix WainwrightHDS.NucNorm

end BrouwerLaplacian.Dev.OpN
end

section
namespace BrouwerLaplacian.Dev.NLem

open Finset Matrix BrouwerLaplacian

theorem cent_apply {n : ℕ} (i j : Fin n) :
    centering n i j = (if i = j then 1 else 0) - (n : ℝ)⁻¹ := by
  simp [centering, onesMat, Matrix.one_apply]

theorem cent_symm {n : ℕ} (i j : Fin n) : centering n j i = centering n i j := by
  rw [cent_apply, cent_apply]; simp [eq_comm]

theorem cent_mulVec {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    (centering n *ᵥ x) i = x i - (n : ℝ)⁻¹ * ∑ j, x j := by
  simp only [Matrix.mulVec, dotProduct, cent_apply, sub_mul, sum_sub_distrib, ite_mul, one_mul,
    zero_mul, sum_ite_eq, mem_univ, if_true]
  rw [← mul_sum]

end BrouwerLaplacian.Dev.NLem

namespace BrouwerLaplacian
open Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.L56

open Finset Matrix BrouwerLaplacian

theorem sumv {n : ℕ} (w : Fin n → ℝ) : ∑ i, (centering n *ᵥ w) i = 0 := by
  by_cases hn : n = 0
  · subst hn; simp
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp only [NLem.cent_mulVec, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp; ring

end BrouwerLaplacian.Dev.L56

namespace BrouwerLaplacian
open Finset Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.L53

open Finset Matrix BrouwerLaplacian

theorem M_symm {n k : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsOrthProj P k) (i j : Fin n) :
    routingM P i j = routingM P j i := by
  by_cases hij : i = j
  · subst hij; rfl
  · have : ¬ j = i := fun h => hij h.symm
    simp [routingM, hij, this, L52.symm_of hP i j]; ring

end BrouwerLaplacian.Dev.L53

namespace BrouwerLaplacian
open Finset Matrix
end BrouwerLaplacian
end

section
namespace BrouwerLaplacian.Dev.NucSym

open Matrix Polynomial Finset WainwrightHDS.NucNorm

theorem charpoly_sq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    (A * A).charpoly = ∏ i, (X - C ((hA.eigenvalues i) ^ 2)) := by
  have h1 : A * A = Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (diagonal (RCLike.ofReal ∘ hA.eigenvalues) * diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := by
    rw [map_mul, ← hA.spectral_theorem]
  conv_lhs => rw [h1, Unitary.conjStarAlgAut_apply, charpoly_mul_comm, ← mul_assoc]
  simp [charpoly_diagonal, diagonal_mul_diagonal, sq]

theorem eig_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {m : ℕ} {S S' : E →ₗ[ℝ] E} (h : S = S') (hS : S.IsSymmetric) (hS' : S'.IsSymmetric)
    (hm : Module.finrank ℝ E = m) : hS.eigenvalues hm = hS'.eigenvalues hm := by
  subst h; rfl

theorem multiset_sq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (hA2 : (A * A).IsHermitian) :
    (univ : Finset (Fin n)).val.map hA2.eigenvalues
      = (univ : Finset (Fin n)).val.map (fun i => (hA.eigenvalues i) ^ 2) := by
  have h1 := hA2.roots_charpoly_eq_eigenvalues
  rw [charpoly_sq hA, Polynomial.roots_prod] at h1
  · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton] at h1
    rw [h1]
    simp [Function.comp_def]
  · exact Finset.prod_ne_zero_iff.2 fun i _ => X_sub_C_ne_zero _

theorem nuc_eq_sum_abs {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    nucNorm A = ∑ i, |hA.eigenvalues i| := by
  have hA2 : (A * A).IsHermitian := by
    have := Matrix.isHermitian_mul_conjTranspose_self A
    rwa [hA.eq] at this
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := finrank_euclideanSpace
  have hadj : LinearMap.adjoint (Matrix.toEuclideanLin A) ∘ₗ Matrix.toEuclideanLin A = Matrix.toEuclideanLin (A * A) := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hA.eq]
    exact (Matrix.toLpLin_mul 2 2 2 A A).symm
  have hsv : ∀ i : Fin (Fintype.card (Fin n)),
      (Matrix.toEuclideanLin A).singularValues i = √(hA2.eigenvalues₀ i) := by
    intro i
    rw [(Matrix.toEuclideanLin A).singularValues_fin hn i]
    congr 1
    exact eig_congr hadj _ _ hn ▸ rfl
  unfold nucNorm singVal
  rw [min_self, show Finset.range n = Finset.range (Fintype.card (Fin n)) from by
    rw [Fintype.card_fin], Finset.sum_range]
  simp only [hsv]
  rw [← (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))).symm.sum_comp]
  have hm := multiset_sq hA hA2
  have key : ∀ i : Fin n, √(hA2.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))).symm i))
      = √(hA2.eigenvalues i) := fun i => rfl
  simp only [key]
  show (Multiset.map (fun i => √(hA2.eigenvalues i)) univ.val).sum
    = (Multiset.map (fun i => |hA.eigenvalues i|) univ.val).sum
  have h2 : (fun i => √(hA2.eigenvalues i)) = (fun x => √x) ∘ hA2.eigenvalues := rfl
  rw [h2, ← Multiset.map_map, hm, Multiset.map_map]
  congr 2
  funext i
  simp [Real.sqrt_sq_eq_abs]

end BrouwerLaplacian.Dev.NucSym
end

section
namespace BrouwerLaplacian.Dev.Duality

open Matrix Finset WainwrightHDS.NucNorm

theorem trace_eq_euclid {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    M.trace = (Matrix.toEuclideanLin M).trace ℝ (EuclideanSpace ℝ (Fin n)) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
    Pi.single_apply]

theorem abs_trace_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (N : Matrix (Fin n) (Fin n) ℝ) :
    |(A * N).trace| ≤ nucNorm A * opNorm2 N := by
  rw [NucSym.nuc_eq_sum_abs hA, trace_eq_euclid, Finset.sum_mul]
  rw [LinearMap.trace_eq_sum_inner _ hA.eigenvectorBasis]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  have hb := hA.eigenvectorBasis.orthonormal.1 i
  have hT : (Matrix.toEuclideanLin A).IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.2 hA
  have h1 : inner ℝ (hA.eigenvectorBasis i) ((Matrix.toEuclideanLin (A * N)) (hA.eigenvectorBasis i))
      = hA.eigenvalues i * inner ℝ (hA.eigenvectorBasis i) ((Matrix.toEuclideanLin N) (hA.eigenvectorBasis i)) := by
    have e1 : (Matrix.toEuclideanLin (A * N)) (hA.eigenvectorBasis i)
        = Matrix.toEuclideanLin A ((Matrix.toEuclideanLin N) (hA.eigenvectorBasis i)) := by
      ext j
      simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
    rw [e1, ← hT (hA.eigenvectorBasis i), ← real_inner_smul_left]
    congr 1
    have := hA.mulVec_eigenvectorBasis i
    ext j
    simp [Matrix.toEuclideanLin_apply, this]
  rw [h1, abs_mul]
  gcongr
  have hnb : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  refine (abs_real_inner_le_norm _ _).trans ?_
  have := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin N)).le_opNorm (hA.eigenvectorBasis i)
  rw [hnb] at this ⊢
  simpa [opNorm2] using this

end BrouwerLaplacian.Dev.Duality
end

section
namespace BrouwerLaplacian.Dev.CutLem

open Finset

theorem split3 {n : ℕ} (i : Fin n) (f : Fin n → ℝ) :
    ∑ j, f j = ∑ j with i < j, f j + ∑ j with j < i, f j + f i := by
  simp only [sum_filter]
  have : ∀ j, f j = (if i < j then f j else 0) + (if j < i then f j else 0)
      + (if j = i then f j else 0) := by
    intro j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne', not_lt_of_gt h]
    · subst h; simp
    · simp [h, h.ne, not_lt_of_gt h]
  conv_lhs => rw [sum_congr rfl fun j _ => this j]
  rw [sum_add_distrib, sum_add_distrib]
  simp

theorem full_split {n : ℕ} (g : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, g i j = ∑ i, ∑ j with i < j, (g i j + g j i) + ∑ i, g i i := by
  have h1 : ∀ i, ∑ j, g i j = ∑ j with i < j, g i j + ∑ j with j < i, g i j + g i i :=
    fun i => split3 i (g i)
  simp only [h1, sum_add_distrib]
  have h2 : ∑ i, ∑ j with j < i, g i j = ∑ i, ∑ j with i < j, g j i := by
    simp only [sum_filter]
    rw [sum_comm]
  rw [h2]

theorem nonneg_case {n : ℕ} (c : Fin n → Fin n → ℝ) (hc0 : ∀ i j, 0 ≤ c i j)
    (hcs : ∀ i j, c i j = c j i) (v : Fin n → ℝ)
    (hcut : ∀ K : Finset (Fin n), ∑ i ∈ K, v i ≤ ∑ i ∈ K, ∑ j ∈ Kᶜ, c i j) :
    ∀ s : ℕ, ∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) → (univ.filter fun i => y i ≠ 0).card = s →
      ∑ i, y i * v i ≤ ∑ i, ∑ j with i < j, c i j * |y i - y j| := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro y hy hs
  by_cases hT : (univ.filter fun i => y i ≠ 0) = ∅
  · have h0 : ∀ i, y i = 0 := by
      intro i; by_contra h
      have : i ∈ univ.filter (fun i => y i ≠ 0) := by simp [h]
      rw [hT] at this; simp at this
    simp [h0]
  · set T := univ.filter fun i => y i ≠ 0 with hTdef
    have hne : T.Nonempty := Finset.nonempty_iff_ne_empty.2 hT
    obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image T y hne
    set δ := y i0 with hδdef
    have hδ : 0 < δ := lt_of_le_of_ne (hy i0) (fun h => (mem_filter.1 hi0).2 h.symm)
    have hyT : ∀ i, i ∈ T → δ ≤ y i := fun i hi => hmin i hi
    have hyN : ∀ i, i ∉ T → y i = 0 := by
      intro i hi; by_contra h; exact hi (by simp [hTdef, h])
    set y' : Fin n → ℝ := fun i => y i - if i ∈ T then δ else 0 with hy'def
    have hy' : ∀ i, 0 ≤ y' i := by
      intro i; by_cases hi : i ∈ T
      · simp [hy'def, hi, hyT i hi]
      · simp [hy'def, hi, hy i]
    have hcard : (univ.filter fun i => y' i ≠ 0).card < s := by
      rw [← hs]
      apply Finset.card_lt_card
      refine ⟨fun i hi => ?_, fun h => ?_⟩
      · have : y' i ≠ 0 := (mem_filter.1 hi).2
        by_contra hiT
        apply this; simp [hy'def, hiT, hyN i hiT]
      · have := h hi0
        have := (mem_filter.1 this).2
        apply this; simp [hy'def, hi0, hδdef]
    have ih' := ih _ hcard y' hy' rfl
    have hcutT := hcut T
    -- left side
    have hL : ∑ i, y i * v i = ∑ i, y' i * v i + δ * ∑ i ∈ T, v i := by
      have : ∀ i, y i * v i = y' i * v i + δ * (if i ∈ T then v i else 0) := by
        intro i; by_cases hi : i ∈ T <;> simp [hy'def, hi] <;> ring
      simp only [this, sum_add_distrib, ← mul_sum, sum_ite_mem, univ_inter]
    -- right side pointwise
    have hpt : ∀ i j, i < j → c i j * |y' i - y' j|
        + δ * (c i j * ((if i ∈ T ∧ j ∉ T then 1 else 0) + (if j ∈ T ∧ i ∉ T then 1 else 0)))
        ≤ c i j * |y i - y j| := by
      intro i j hij
      have key : |y' i - y' j| + δ * ((if i ∈ T ∧ j ∉ T then 1 else 0) + (if j ∈ T ∧ i ∉ T then 1 else 0))
          ≤ |y i - y j| := by
        by_cases hi : i ∈ T <;> by_cases hj : j ∈ T
        · simp [hy'def, hi, hj]
        · have e1 := hyT i hi; have e2 := hyN j hj
          have e3 := hy' i
          simp only [hy'def, hi, hj, e2, if_true, if_false, and_true, true_and, not_true_eq_false,
            and_false, not_false_eq_true, sub_zero, add_zero]
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          linarith
        · have e1 := hyT j hj; have e2 := hyN i hi
          simp only [hy'def, hi, hj, e2, if_true, if_false, and_true, true_and, not_true_eq_false,
            and_false, not_false_eq_true, sub_zero, zero_add]
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
          linarith
        · simp [hy'def, hi, hj, hyN i hi, hyN j hj]
      calc c i j * |y' i - y' j| + δ * (c i j * _) = c i j * (|y' i - y' j| + δ * ((if i ∈ T ∧ j ∉ T then 1 else 0) + (if j ∈ T ∧ i ∉ T then 1 else 0))) := by ring
        _ ≤ c i j * |y i - y j| := mul_le_mul_of_nonneg_left key (hc0 i j)
    have hsum : ∑ i, ∑ j with i < j, (c i j * |y' i - y' j|
        + δ * (c i j * ((if i ∈ T ∧ j ∉ T then 1 else 0) + (if j ∈ T ∧ i ∉ T then 1 else 0))))
        ≤ ∑ i, ∑ j with i < j, c i j * |y i - y j| := by
      refine sum_le_sum fun i _ => sum_le_sum fun j hj => hpt i j (mem_filter.1 hj).2
    have hcutsum : ∑ i, ∑ j with i < j, δ * (c i j *
        ((if i ∈ T ∧ j ∉ T then 1 else 0) + (if j ∈ T ∧ i ∉ T then 1 else 0)))
        = δ * ∑ i ∈ T, ∑ j ∈ Tᶜ, c i j := by
      have hfs := full_split (fun i j => c i j * (if i ∈ T ∧ j ∉ T then (1 : ℝ) else 0))
      have e1 : ∑ i, ∑ j, c i j * (if i ∈ T ∧ j ∉ T then (1 : ℝ) else 0)
          = ∑ i ∈ T, ∑ j ∈ Tᶜ, c i j := by
        have : ∀ i, ∑ j, c i j * (if i ∈ T ∧ j ∉ T then (1 : ℝ) else 0)
            = if i ∈ T then ∑ j ∈ Tᶜ, c i j else 0 := by
          intro i
          by_cases hi : i ∈ T
          · simp only [hi, true_and, if_true, mul_ite, mul_one, mul_zero]
            rw [← sum_filter]
            congr 1; ext j; simp
          · simp [hi]
        simp only [this]
        rw [sum_ite_mem]; simp
      have e2 : ∑ i, c i i * (if i ∈ T ∧ i ∉ T then (1 : ℝ) else 0) = 0 := by simp
      have e3 : ∀ i j, c i j * (if i ∈ T ∧ j ∉ T then (1 : ℝ) else 0)
          + c j i * (if j ∈ T ∧ i ∉ T then (1 : ℝ) else 0)
          = c i j * ((if i ∈ T ∧ j ∉ T then 1 else 0) + (if j ∈ T ∧ i ∉ T then 1 else 0)) := by
        intro i j; rw [hcs j i]; ring
      simp only [e3, e2, add_zero] at hfs
      rw [e1] at hfs
      rw [hfs]
      simp only [mul_sum]
    have hsplit : ∑ i, ∑ j with i < j, (c i j * |y' i - y' j|
        + δ * (c i j * ((if i ∈ T ∧ j ∉ T then 1 else 0) + (if j ∈ T ∧ i ∉ T then 1 else 0))))
        = ∑ i, ∑ j with i < j, c i j * |y' i - y' j| + ∑ i, ∑ j with i < j, δ * (c i j *
        ((if i ∈ T ∧ j ∉ T then 1 else 0) + (if j ∈ T ∧ i ∉ T then 1 else 0))) := by
      simp only [sum_add_distrib]
    rw [hL]
    rw [hsplit, hcutsum] at hsum
    nlinarith [mul_le_mul_of_nonneg_left hcutT hδ.le]

theorem cut_bound {n : ℕ} (c : Fin n → Fin n → ℝ) (hc0 : ∀ i j, 0 ≤ c i j)
    (hcs : ∀ i j, c i j = c j i) (v : Fin n → ℝ) (hv : ∑ i, v i = 0)
    (hcut : ∀ K : Finset (Fin n), ∑ i ∈ K, v i ≤ ∑ i ∈ K, ∑ j ∈ Kᶜ, c i j)
    (x : Fin n → ℝ) :
    ∑ i, x i * v i ≤ ∑ i, ∑ j with i < j, c i j * |x i - x j| := by
  by_cases hn : n = 0
  · subst hn; simp
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  obtain ⟨i0, -, hmin⟩ := Finset.exists_min_image (univ : Finset (Fin n)) x univ_nonempty
  set m := x i0
  have hy : ∀ i, 0 ≤ x i - m := fun i => sub_nonneg.2 (hmin i (mem_univ i))
  have := nonneg_case c hc0 hcs v hcut _ (fun i => x i - m) hy rfl
  have e1 : ∑ i, (x i - m) * v i = ∑ i, x i * v i := by
    simp only [sub_mul, sum_sub_distrib, ← mul_sum, hv, mul_zero, sub_zero]
  have e2 : ∀ i j, (x i - m) - (x j - m) = x i - x j := fun i j => by ring
  simp only [e1, e2] at this
  exact this

end BrouwerLaplacian.Dev.CutLem
end

section
namespace BrouwerLaplacian.Dev.L55

open Finset Matrix BrouwerLaplacian

theorem psd_form {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q * Q = Q) (hQs : ∀ i j, Q j i = Q i j)
    (i j : Fin n) : 0 ≤ Q i i + Q j j - 2 * Q i j := by
  have h : ∀ a b, Q a b = ∑ k, Q k a * Q k b := by
    intro a b
    have := congrFun (congrFun hQ a) b
    rw [Matrix.mul_apply] at this
    rw [← this]
    exact sum_congr rfl fun k _ => by rw [hQs a k]
  have : Q i i + Q j j - 2 * Q i j = ∑ k, (Q k i - Q k j) ^ 2 := by
    have e : ∀ k, (Q k i - Q k j) ^ 2 = Q k i * Q k i + Q k j * Q k j - 2 * (Q k i * Q k j) := by
      intro k; ring
    simp only [e, sum_sub_distrib, sum_add_distrib, ← mul_sum]
    rw [← h i i, ← h j j, ← h i j]
  rw [this]; exact sum_nonneg fun k _ => sq_nonneg _

theorem cap_nonneg {n k : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsOrthProj P k) (i j : Fin n) :
    0 ≤ 1 - |routingM P i j| := by
  by_cases hij : i = j
  · subst hij; simp [routingM]
  have ha := psd_form hP.2.1 (L52.symm_of hP) i j
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hP.2.1]; simp
  have hQs : ∀ a b, (1 - P) b a = (1 - P) a b := by
    intro a b; simp [Matrix.one_apply, L52.symm_of hP a b, eq_comm]
  have hb := psd_form hQ hQs i j
  simp [Matrix.one_apply, hij] at hb
  have : routingM P i j = P i i + P j j - 2 * P i j - 1 := by simp [routingM, hij]
  rw [this]
  have : |P i i + P j j - 2 * P i j - 1| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  linarith

theorem split_with {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (K : Finset (Fin n)) :
    IsSplitWith (splitGraphOf A K) K := by
  refine ⟨fun i hi j hj hij => ⟨hij, Or.inl ⟨hi, hj⟩⟩, fun i hi j hj hij h => ?_⟩
  have hi' : i ∉ K := by simpa using hi
  have hj' : j ∉ K := by simpa using hj
  obtain ⟨-, h | h | h⟩ := h
  · exact hi' h.1
  · exact hi' h.1
  · exact hj' h.1

theorem hermitian_A {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℝ) :
    (G.lapMatrix ℝ - r • centering n).IsHermitian := by
  have hC : (centering n).IsHermitian := by
    ext i j; simpa using NLem.cent_symm i j
  have hC' : (r • centering n).IsHermitian := by
    ext i j; simp [Matrix.conjTranspose_apply, NLem.cent_symm i j]
  exact (G.isHermitian_lapMatrix ℝ).sub hC'

theorem cut_cond {n k : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) (K : Finset (Fin n)) :
    ∑ i ∈ K, routingV P i ≤ ∑ i ∈ K, ∑ j ∈ Kᶜ, (1 - |routingM P i j|) := by
  have hv : ∑ i, routingV P i = 0 := L56.sumv _
  by_cases hK0 : K = ∅
  · subst hK0; simp
  by_cases hKu : K = univ
  · subst hKu; simp [hv]
  have hKc : 1 ≤ #K := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hK0)
  have hKn : #K ≤ n - 1 := by
    have : #K < n := by
      have := Finset.card_lt_card (Finset.ssubset_univ_iff.2 hKu)
      simpa using this
    omega
  have h53 := BrouwerLaplacian.eq_5_3 P hP hP1 K hKc hKn
  have hA := hermitian_A (splitGraphOf (routingM P) K) (#K : ℝ)
  have h32 := BrouwerLaplacian.lemma_3_2 (splitGraphOf (routingM P) K) K (split_with _ K)
  have hdual := Duality.abs_trace_le hA (routingN P)
  have hN := (BrouwerLaplacian.proof_lemma_5_5_N P hP hP1).2.2.2.2.1
  have hnuc : 0 ≤ WainwrightHDS.NucNorm.nucNorm
      ((splitGraphOf (routingM P) K).lapMatrix ℝ - (#K : ℝ) • centering n) := by
    rw [NucSym.nuc_eq_sum_abs hA]; exact sum_nonneg fun i _ => abs_nonneg _
  have hcompl : (#Kᶜ : ℝ) = n - #K := by
    rw [Finset.card_compl, Fintype.card_fin, Nat.cast_sub (by omega)]
  have hbound : ∑ i ∈ K, routingV P i + ∑ i ∈ K, ∑ j ∈ Kᶜ, |routingM P i j|
      ≤ (#K : ℝ) * (#Kᶜ : ℝ) := by
    rw [h53]
    calc _ ≤ |Matrix.trace (((splitGraphOf (routingM P) K).lapMatrix ℝ - (#K : ℝ) • centering n)
          * routingN P)| := by exact neg_le_abs _
      _ ≤ _ := hdual
      _ ≤ _ := by nlinarith
  have : ∑ i ∈ K, ∑ j ∈ Kᶜ, (1 - |routingM P i j|) = (#K : ℝ) * (#Kᶜ : ℝ) - ∑ i ∈ K, ∑ j ∈ Kᶜ, |routingM P i j| := by
    simp [sum_sub_distrib, sum_const, nsmul_eq_mul]
  linarith

theorem main {n k : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) :
    (∀ x : Fin n → ℝ, |∑ i, x i * routingV P i|
        ≤ ∑ i, ∑ j with i < j, (1 - |routingM P i j|) * |x i - x j|) ∧
    ∑ i, ∑ j with i < j, (1 - |routingM P i j|) * |routingV P i - routingV P j|
      ≥ ∑ i, routingV P i ^ 2 := by
  have hv : ∑ i, routingV P i = 0 := L56.sumv _
  have hcb := fun x => CutLem.cut_bound (fun i j => 1 - |routingM P i j|) (cap_nonneg hP)
    (fun i j => by rw [L53.M_symm hP i j]) (routingV P) hv (cut_cond P hP hP1) x
  have h1 : ∀ x : Fin n → ℝ, |∑ i, x i * routingV P i|
      ≤ ∑ i, ∑ j with i < j, (1 - |routingM P i j|) * |x i - x j| := by
    intro x
    rw [abs_le]
    constructor
    · have := hcb (fun i => - x i)
      simp only [neg_mul, sum_neg_distrib, abs_neg, neg_sub_neg] at this
      have e : ∀ i j, |x j - x i| = |x i - x j| := fun i j => abs_sub_comm _ _
      simp only [e] at this
      linarith
    · have := hcb x
      simpa using this
  refine ⟨h1, ?_⟩
  have := h1 (routingV P)
  have e : ∑ i, routingV P i * routingV P i = ∑ i, routingV P i ^ 2 :=
    sum_congr rfl fun i _ => (sq _).symm
  rw [e] at this
  exact le_trans (le_abs_self _) this

end BrouwerLaplacian.Dev.L55

namespace BrouwerLaplacian
open Finset Matrix
theorem chk_lemma_5_5 {n k : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : IsOrthProj P k)
    (hP1 : P *ᵥ (fun _ => 1) = 0) :
    (∀ x : Fin n → ℝ, |∑ i, x i * routingV P i|
        ≤ ∑ i, ∑ j with i < j, (1 - |routingM P i j|) * |x i - x j|) ∧
    ∑ i, ∑ j with i < j, (1 - |routingM P i j|) * |routingV P i - routingV P j|
      ≥ ∑ i, routingV P i ^ 2 := Dev.L55.main P hP hP1
end BrouwerLaplacian
end

theorem solution : type_of% @BrouwerLaplacian.chk_lemma_5_5 := @BrouwerLaplacian.chk_lemma_5_5
