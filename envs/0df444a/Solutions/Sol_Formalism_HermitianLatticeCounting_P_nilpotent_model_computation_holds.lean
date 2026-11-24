-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.nilpotent_model_computation_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:36.648652+00:00
-- url     : https://prove2.me/submissions/449d7cc0-b4a7-410c-b34d-24ed067ccc8f

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_matrix_action_evaluation_holds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_lie_algebra_nilpotent_part_holds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_hL_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_UH_of_isom
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_Hh
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_gram_f
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_herm_e
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_fvec_lt
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_matrix_eq_of_forall_mulVec_eq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_exp_add
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gj_fvec_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gk_herm_add_left
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gk_herm_add_right
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gk_herm_smul_left
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gk_herm_smul_right
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_rank_two_operator_skew_hermitian
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_nset_iff
import Theorems.Thm_Formalism_QuantumDeterminants_fvec_apply_lt
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_swap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate TensorProduct
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WeylGroupFacts
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : RankTwoNilpotentGroup := by
  intro k r z hz a e v he hv
  set H := Hpk k r with hHdef
  have hH : Hᴴ = H := s1c2_Hh k r
  set Y := rankTwoSkewMatrix H e v with hY
  obtain ⟨heX, hX, hYf, hY0, -, hYe, hYv⟩ := lie_algebra_nilpotent_part_holds _ (hermitianSesquilinearForm H)
    (fun x y => by simp only [s1c2_hL_apply]; exact ggHerm_swap _ hH y x) r (fvec k r z) (Tz k r z)
    (fun b c => by simp only [s1c2_hL_apply]; exact s1c2_gram_f k r z hz b c) a e v he
    (fun b hb => by simp only [s1c2_hL_apply]; exact hv b hb)
  have hYx : ∀ x, Y *ᵥ x = rankTwoSkewOperator (hermitianSesquilinearForm H) e v x := fun x => matrix_action_evaluation_holds _ H e v x
  have hYx' : ∀ x, Y *ᵥ x = herm H x v • e - herm H x e • v := fun x => matrix_action_evaluation_holds _ H e v x
  have hYe' : Y *ᵥ e = 0 := by rw [hYx]; exact hYe
  have hYv' : Y *ᵥ v = herm H v v • e := by rw [hYx]; exact hYv
  have hYY : ∀ x, Y *ᵥ (Y *ᵥ x) = (-(herm H x e * herm H v v)) • e := by
    intro x
    rw [hYx' x, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hYe', hYv', smul_zero, zero_sub,
      smul_smul, neg_smul]
  have h3 : Y * Y * Y = 0 := by
    apply matrix_eq_of_forall_mulVec_eq
    intro x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hYx' x, Matrix.mulVec_sub, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hYe', hYv', Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hYe']
    simp
  have hadd : ∀ s t : ℝ, nilpotentExpSquare H e v (s + t) = nilpotentExpSquare H e v s * nilpotentExpSquare H e v t := by
    intro s t
    unfold nilpotentExpSquare
    rw [← hY]
    push_cast
    exact s1c2_exp_add Y h3 s t
  have hEx : ∀ (t : ℝ) x, nilpotentExpSquare H e v t *ᵥ x = x + (t : ℂ) • (Y *ᵥ x) + ((t : ℂ) ^ 2 / 2) • (Y *ᵥ (Y *ᵥ x)) := by
    intro t x
    unfold nilpotentExpSquare
    rw [← hY, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.mulVec_mulVec]
  have hskew : ∀ x y, herm H (Y *ᵥ x) y = -herm H x (Y *ᵥ y) := by
    intro x y
    have := rank_two_operator_skew_hermitian _ (hermitianSesquilinearForm H)
      (fun x y => by simp only [s1c2_hL_apply]; exact ggHerm_swap _ hH y x) e v x y
    simp only [s1c2_hL_apply] at this
    rw [hYx' x, hYx' y]
    exact eq_neg_of_add_eq_zero_left this
  have hadj : ∀ (t : ℝ) x y, herm H (nilpotentExpSquare H e v t *ᵥ x) y = herm H x (nilpotentExpSquare H e v (-t) *ᵥ y) := by
    intro t x y
    rw [hEx, hEx]
    simp only [gk_herm_add_left, gk_herm_add_right, gk_herm_smul_left, gk_herm_smul_right, hskew]
    have c1 : star (((-t : ℝ) : ℂ)) = -(t : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]; push_cast; ring
    have c2 : star (((-t : ℝ) : ℂ) ^ 2 / 2) = (t : ℂ) ^ 2 / 2 := by
      have e2 : (((-t : ℝ) : ℂ) ^ 2 / 2) = (((t ^ 2 / 2 : ℝ)) : ℂ) := by push_cast; ring
      rw [e2, Complex.star_def, Complex.conj_ofReal]; push_cast; ring
    rw [c1, c2]; ring
  have hE0 : nilpotentExpSquare H e v 0 = 1 := by simp [nilpotentExpSquare]
  have hUH : ∀ t : ℝ, nilpotentExpSquare H e v t ∈ UH H := by
    intro t
    apply s1c2_UH_of_isom
    intro x y
    rw [hadj, Matrix.mulVec_mulVec, ← hadd, neg_add_cancel, hE0, Matrix.one_mulVec]

  have hsupp : ∀ y ∈ Submodule.span ℂ (fvec k r z '' {b | b < a.castSucc}),
      ∀ i : Fin (2 * r + k + 1), a.val ≤ i.val → y i = 0 := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ => ∀ i : Fin (2 * r + k + 1), a.val ≤ i.val → y i = 0)
      ?_ ?_ ?_ ?_ hy
    · rintro y ⟨b, hb, rfl⟩ i hi
      have hb' : b.val < a.val := hb
      rw [gj_fvec_apply k r z b (by omega), if_neg (by omega)]
    · intro i _; rfl
    · intro y w _ _ h1 h2 i hi; rw [Pi.add_apply, h1 i hi, h2 i hi, add_zero]
    · intro c y _ h1 i hi; rw [Pi.smul_apply, h1 i hi, smul_zero]
  have hei : ∀ i : Fin (2 * r + k + 1), a.val ≤ i.val → e i = if i.val = a.val then 1 else 0 := by
    intro i hi
    have h1 := hsupp _ he i hi
    rw [Pi.sub_apply, sub_eq_zero] at h1
    rw [h1, gj_fvec_apply k r z a.castSucc (by simp)]
    rfl

  have hEperp : ∀ (t : ℝ) x, (∀ b : Fin r, herm H x (fvec k r z b.castSucc) = 0) →
      nilpotentExpSquare H e v t *ᵥ x = x + ((t : ℂ) * herm H x v) • e := by
    intro t x hx
    have h1 : Y *ᵥ x = herm H x v • e := by rw [hYx]; exact hX x hx
    rw [hEx, h1, Matrix.mulVec_smul, hYe', smul_zero, smul_zero, add_zero, smul_smul]
  have hEf : ∀ (t : ℝ) b, nilpotentExpSquare H e v t *ᵥ fvec k r z b = fvec k r z b + ((t : ℂ) * herm H (fvec k r z b) v) • e := by
    intro t b
    have h1 : Y *ᵥ fvec k r z b = herm H (fvec k r z b) v • e := by rw [hYx]; exact hYf b
    rw [hEx, h1, Matrix.mulVec_smul, hYe', smul_zero, smul_zero, add_zero, smul_smul]
  refine ⟨h3, hadd, fun t => ⟨?_, ?_⟩⟩
  · rw [nset_iff]
    refine ⟨hUH t, ?_⟩
    intro i j hj hij
    have hcolj : nilpotentExpSquare H e v t i j = (nilpotentExpSquare H e v t *ᵥ bvec j) i := by
      simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
    have hperp : ∀ b : Fin r, herm H (bvec j) (fvec k r z b.castSucc) = 0 := by
      intro b
      rw [s1c2_fvec_lt k r z b.castSucc (by simp), s1c2_herm_e]
      simp only [bvec, Pi.single_apply, esI]
      rw [if_neg]
      intro h'
      have := congrArg Fin.val h'
      simp at this
      omega
    rw [hcolj, hEperp t _ hperp, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hz0 : (t : ℂ) * herm H (bvec j) v * e i = 0 := by
      by_cases hia : i.val ≤ a.val
      · have hja : j.val ≤ a.val := by
          rcases hij with h | h
          · omega
          · have := a.isLt; omega
        have hjr : j.val < r := lt_of_le_of_lt hja a.isLt
        have hbj : bvec j = fvec k r z ⟨j.val, by omega⟩ := by
          rw [s1c2_fvec_lt k r z ⟨j.val, by omega⟩ hjr]; rfl
        rw [hbj, hv ⟨j.val, by omega⟩ (by rw [Fin.le_def]; simpa using hja), mul_zero, zero_mul]
      · rw [hei i (by omega), if_neg (by omega), mul_zero]
    rw [hz0, add_zero]
    simp only [bvec, Pi.single_apply]
  · unfold ell
    have hterm : ∀ b : Fin r, (if h : b.val + 1 < r then nilpotentExpSquare H e v t (eI k r b) (eI k r ⟨b.val + 1, h⟩)
        else (nilpotentExpSquare H e v t *ᵥ z) (eI k r b)) = (nilpotentExpSquare H e v t *ᵥ fvec k r z b.succ) (eI k r b) := by
      intro b
      split_ifs with h
      · rw [s1c2_fvec_lt k r z b.succ (by simpa using h)]
        simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
      · have : fvec k r z b.succ = z := by
          simp [fvec, h]
        rw [this]
    rw [Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_eq_single a]
    · rw [hEf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hei _ (by simp [eI]), if_pos (by simp [eI]),
        fvec_apply_lt z hz _ _ (by simp [eI]), if_neg (by simp [eI]), zero_add, mul_one]
    · intro b _ hb
      rw [hEf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, fvec_apply_lt z hz _ _ (by simp [eI]),
        if_neg (by simp [eI]), zero_add]
      rcases lt_or_gt_of_ne hb with h | h
      · rw [hv b.succ (by rw [Fin.le_def]; simpa using h), mul_zero, zero_mul]
      · have h' : a.val < b.val := h
        rw [hei _ (by simp only [eI]; omega), if_neg (by simp only [eI]; omega), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.HermitianLatticeCounting.P
