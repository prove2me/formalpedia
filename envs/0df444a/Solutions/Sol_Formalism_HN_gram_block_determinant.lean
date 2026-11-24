-- Prove2me | solution 1 for Formalism.HN.gram_block_determinant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:06.892195+00:00
-- url     : https://prove2.me/submissions/c774687a-d3a4-426c-b430-ff603a98dd2c

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Theorems.Thm_Formalism_HN_gramBlock_norm_sum_sq
import Theorems.Thm_Formalism_HN_gramBlock_gram_comb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module
noncomputable section
namespace Formalism.HN
private theorem det_gram_le_one_of_norm_sum_sq_le {κ F : Type*} [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (w : κ → F)
    (hw : ∀ x : κ → ℝ, ‖∑ a, x a • w a‖ ^ 2 ≤ ∑ a, x a ^ 2) :
    (Matrix.gram ℝ w).det ≤ 1 := by
  have hP := Matrix.posSemidef_gram ℝ w
  rw [hP.isHermitian.det_eq_prod_eigenvalues]
  apply Finset.prod_le_one
  · intro i _
    simpa using hP.eigenvalues_nonneg i
  · intro i _
    have hv : ∑ a, (hP.isHermitian.eigenvectorBasis i).ofLp a ^ 2 = 1 := by
      have h1 := PiLp.norm_sq_eq_of_L2 (fun _ : κ => ℝ) (hP.isHermitian.eigenvectorBasis i)
      rw [hP.isHermitian.eigenvectorBasis.orthonormal.1 i] at h1
      simpa [Real.norm_eq_abs, sq_abs] using h1.symm
    have h2 := hP.isHermitian.eigenvalues_eq i
    rw [Matrix.star_dotProduct_gram_mulVec, RCLike.re_to_real, real_inner_self_eq_norm_sq] at h2
    simp only [RCLike.ofReal_real_eq_id, id]
    rw [h2, ← hv]
    exact hw _
end Formalism.HN
end
end

set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution : GramBlock := by
  intro P E E' ι _ _ _ _ _ _ _ _ _ _ Ev Ev' T c W u hEv hEv' hc hT hW hu hspan
  classical
  let k : P → ℕ := fun v => Module.finrank ℝ (W ⊓ Ev v : Submodule ℝ E)
  let B : ∀ v, OrthonormalBasis (Fin (k v)) ℝ (W ⊓ Ev v : Submodule ℝ E) :=
    fun v => stdOrthonormalBasis ℝ _
  let f : (Σ v, Fin (k v)) → E := fun a => (B a.1 a.2 : E)
  have hfW : ∀ a, f a ∈ W ⊓ Ev a.1 := fun a => (B a.1 a.2).2
  have hfon : Orthonormal ℝ f := by
    rw [orthonormal_iff_ite]
    rintro ⟨v, i⟩ ⟨w, j⟩
    by_cases hvw : v = w
    · subst hvw
      have h1 := orthonormal_iff_ite.1 (B v).orthonormal i j
      rw [Submodule.coe_inner] at h1
      simp only [f]
      rw [h1]
      by_cases hij : i = j
      · simp [hij]
      · simp [hij]
    · rw [if_neg (fun h => hvw (congrArg Sigma.fst h))]
      exact hEv v w hvw _ (hfW ⟨v, i⟩).2 _ (hfW ⟨w, j⟩).2
  have hspanf : Submodule.span ℝ (Set.range f) = W := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact (hfW a).1
    · conv_lhs => rw [hW]
      refine iSup_le fun v => ?_
      intro x hx
      have key : ((∑ i, inner ℝ (B v i) (⟨x, hx⟩ : (W ⊓ Ev v : Submodule ℝ E)) • B v i :
          (W ⊓ Ev v : Submodule ℝ E)) : E) = x := by
        rw [(B v).sum_repr']
      rw [← key, Submodule.coe_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Submodule.coe_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨v, i⟩, rfl⟩)
  have hcard : Fintype.card (Σ v, Fin (k v)) = Fintype.card ι := by
    have h1 := finrank_span_eq_card hfon.linearIndependent
    have h2 := finrank_span_eq_card hu
    rw [hspanf] at h1
    rw [hspan] at h2
    omega
  let e := Fintype.equivOfCardEq hcard
  let f' : ι → E := f ∘ e.symm
  have hf'on : Orthonormal ℝ f' := hfon.comp _ e.symm.injective
  have hspan' : Submodule.span ℝ (Set.range f') = W := by
    rw [Set.range_comp, e.symm.surjective.range_eq, Set.image_univ]
    exact hspanf
  have hex : ∀ j, ∃ a : ι → ℝ, ∑ i, a i • f' i = u j := by
    intro j
    have : u j ∈ Submodule.span ℝ (Set.range f') := by
      rw [hspan', ← hspan]
      exact Submodule.subset_span ⟨j, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).1 this
  choose a ha using hex
  let M : Matrix ι ι ℝ := fun i j => a j i
  have huM : u = fun j => ∑ i, M i j • f' i := funext fun j => (ha j).symm
  have hG1 : Matrix.gram ℝ f' = 1 := by
    ext i j
    rw [Matrix.gram_apply, orthonormal_iff_ite.1 hf'on, Matrix.one_apply]
  have hGu : (Matrix.gram ℝ u).det = M.det ^ 2 := by
    have h1 := gramBlock_gram_comb (LinearMap.id : E →ₗ[ℝ] E) f' M
    simp only [LinearMap.id_apply] at h1
    simp only [huM]
    rw [h1, hG1, Matrix.mul_one, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hGT : (Matrix.gram ℝ (fun i => T (u i))).det =
      M.det ^ 2 * (Matrix.gram ℝ (fun i => T (f' i))).det := by
    simp only [huM]
    rw [gramBlock_gram_comb T f' M, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hreidx : (Matrix.gram ℝ (fun i => T (f' i))).det =
      (Matrix.gram ℝ (fun a => T (f a))).det := by
    have h1 : Matrix.gram ℝ (fun i => T (f' i)) =
        (Matrix.gram ℝ (fun a => T (f a))).submatrix e.symm e.symm := by
      ext i j
      rfl
    rw [h1, Matrix.det_submatrix_equiv_self]
  have hTf : ∀ a, T (f a) ∈ Ev' a.1 ∧ ‖T (f a)‖ ≤ c a.1 := by
    intro a
    have h1 := hT a.1 (f a) (hfW a).2
    rw [hfon.1 a, mul_one] at h1
    exact h1
  have hprod : ∏ v, c v ^ (2 * Module.finrank ℝ (W ⊓ Ev v : Submodule ℝ E)) =
      ∏ a : (Σ v, Fin (k v)), c a.1 ^ 2 := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun v _ => ?_
    simp [Finset.prod_const, ← pow_mul, k]
  have hA : (Matrix.gram ℝ (fun a => T (f a))).det ≤ ∏ a : (Σ v, Fin (k v)), c a.1 ^ 2 := by
    by_cases h0 : ∃ a : (Σ v, Fin (k v)), c a.1 = 0
    · obtain ⟨a, ha0⟩ := h0
      have hz : T (f a) = 0 := by
        have h1 := (hTf a).2
        rw [ha0] at h1
        exact norm_le_zero_iff.1 h1
      rw [Matrix.det_eq_zero_of_row_eq_zero a (fun j => by rw [Matrix.gram_apply, hz, inner_zero_left])]
      exact Finset.prod_nonneg fun _ _ => sq_nonneg _
    · push_neg at h0
      have hpos : ∀ a : (Σ v, Fin (k v)), 0 < c a.1 := fun a => lt_of_le_of_ne (hc a.1) (h0 a).symm
      let w : (Σ v, Fin (k v)) → E' := fun a => (c a.1)⁻¹ • T (f a)
      have hgram : Matrix.gram ℝ (fun a => T (f a)) =
          Matrix.diagonal (fun a => c a.1) * Matrix.gram ℝ w * Matrix.diagonal (fun a => c a.1) := by
        ext a b
        simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.gram_apply, w,
          real_inner_smul_left, real_inner_smul_right]
        field_simp [(hpos a).ne', (hpos b).ne']
      have hnorm : ∀ x : (Σ v, Fin (k v)) → ℝ, ‖∑ a, x a • w a‖ ^ 2 ≤ ∑ a, x a ^ 2 := by
        intro x
        let z : P → E := fun v => ∑ i, x ⟨v, i⟩ • f ⟨v, i⟩
        let y : P → E' := fun v => (c v)⁻¹ • T (z v)
        have hsum : ∑ a, x a • w a = ∑ v, y v := by
          rw [Fintype.sum_sigma]
          refine Finset.sum_congr rfl fun v _ => ?_
          simp only [y, z, w, map_sum, map_smul, Finset.smul_sum, smul_smul, mul_comm]
        have hzE : ∀ v, z v ∈ Ev v := fun v =>
          Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hfW ⟨v, i⟩).2
        have hyE : ∀ v, y v ∈ Ev' v := fun v => Submodule.smul_mem _ _ (hT v _ (hzE v)).1
        have hyz : ∀ v, ‖y v‖ ≤ ‖z v‖ := by
          intro v
          rcases (hc v).eq_or_lt with h | h
          · simp [y, ← h]
          · have hv := (hT v _ (hzE v)).2
            simp only [y]
            rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h]
            calc (c v)⁻¹ * ‖T (z v)‖ ≤ (c v)⁻¹ * (c v * ‖z v‖) := by gcongr
              _ = ‖z v‖ := by field_simp
        have hzsum : ∑ v, z v = ∑ a, x a • f a := by
          rw [Fintype.sum_sigma]
        rw [hsum, gramBlock_norm_sum_sq y (fun v w hvw => hEv' v w hvw _ (hyE v) _ (hyE w))]
        calc ∑ v, ‖y v‖ ^ 2 ≤ ∑ v, ‖z v‖ ^ 2 :=
              Finset.sum_le_sum fun v _ => pow_le_pow_left₀ (norm_nonneg _) (hyz v) 2
          _ = ‖∑ v, z v‖ ^ 2 :=
              (gramBlock_norm_sum_sq z (fun v w hvw => hEv v w hvw _ (hzE v) _ (hzE w))).symm
          _ = ∑ a, x a ^ 2 := by
              rw [hzsum, ← real_inner_self_eq_norm_sq, hfon.inner_sum x x Finset.univ]
              simp [sq]
      have hle : (Matrix.gram ℝ w).det ≤ 1 := det_gram_le_one_of_norm_sum_sq_le w hnorm
      have hP0 : 0 ≤ ∏ a : (Σ v, Fin (k v)), c a.1 := Finset.prod_nonneg fun a _ => (hpos a).le
      rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
      calc (∏ a : (Σ v, Fin (k v)), c a.1) * (Matrix.gram ℝ w).det * ∏ a : (Σ v, Fin (k v)), c a.1
          ≤ (∏ a : (Σ v, Fin (k v)), c a.1) * 1 * ∏ a : (Σ v, Fin (k v)), c a.1 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hP0) hP0
        _ = ∏ a : (Σ v, Fin (k v)), c a.1 ^ 2 := by
            rw [mul_one, ← Finset.prod_mul_distrib]
            simp [sq]
  refine ⟨?_, fun hiso => ?_⟩
  · rw [hGT, hGu, hreidx, hprod, mul_comm]
    exact mul_le_mul_of_nonneg_right hA (sq_nonneg _)
  · have hdiag : Matrix.gram ℝ (fun a => T (f a)) = Matrix.diagonal (fun a => c a.1 ^ 2) := by
      ext a b
      rw [Matrix.gram_apply, Matrix.diagonal_apply]
      by_cases hab : a.1 = b.1
      · obtain ⟨v, i⟩ := a
        obtain ⟨w, j⟩ := b
        simp only at hab
        subst hab
        rw [hiso v _ (hfW ⟨v, i⟩).2 _ (hfW ⟨v, j⟩).2, orthonormal_iff_ite.1 hfon]
        split_ifs <;> simp
      · rw [if_neg (fun h => hab (congrArg Sigma.fst h))]
        exact hEv' _ _ hab _ (hTf a).1 _ (hTf b).1
    rw [hGT, hGu, hreidx, hdiag, Matrix.det_diagonal, hprod]
    ring
end Formalism.HN
