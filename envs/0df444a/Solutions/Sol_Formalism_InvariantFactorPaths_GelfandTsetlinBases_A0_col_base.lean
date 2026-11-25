-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.col_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:54:22.07588+00:00
-- url     : https://prove2.me/submissions/44dbe4a0-a31c-4d6f-8178-7a4e630b2851

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_wge_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_wge_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_wge_C
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_wge_hom
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_pathWord_card
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_pathWord_congr
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_act_pathWord__f928c95cb9b8
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_wt_word
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_col_bound
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_gam_val
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_gam_inv
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_gH_in
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1hw_map_pathWord
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_minorMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
variable (k : Type) [Field k] {n : ℕ} (isVec : ℕ → Bool) (S : Set ℕ) [DecidablePred (· ∈ S)]
variable {k isVec S}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
theorem _root_.solution {N i : ℕ} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ} (hp : IsPath n isVec B μ N) (hi : i ≤ N)
    (hS : ∀ j, j ∈ S ↔ j < i) (c : ℤ) (last : Bool) (m : Fin n)
    (hm : if last then m.val + 1 = n else m.val = 0) (J : Finset (Fin n)) :
    WGe isVec S last (sgn last)
      (gH k isVec S (pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) k)) i J))
      (sgn last * bc c (μ i m)) := by
  have hm' : ∀ a : Fin n, (if last then a.val + 1 = n else a.val = 0) ↔ a = m := by
    intro a
    cases last
    · simp only [Bool.false_eq_true, if_false] at hm ⊢
      rw [Fin.ext_iff]; omega
    · simp only [if_true] at hm ⊢
      rw [Fin.ext_iff]; omega
  rw [A1hw.map_pathWord (gH k isVec S)]
  rw [pathWord_congr isVec μ c _ _ i fun l hl => gH_in k isVec S ((hS l).2 hl)]
  rw [act_pathWord' isVec μ c
    (fun l b => (X (Sum.inl (l, b)) : MvPolynomial (LVar ℕ Empty n) (GenField k n))) (gam k n _) i]
  refine wge_sum _ _ fun I' _ => ?_
  obtain ⟨z, hz⟩ : ∃ z : GenField k n, minorF (if 1 ≤ c then
      (↑(gam k n (LVar ℕ Empty n)) : Matrix (Fin n) (Fin n) (MvPolynomial (LVar ℕ Empty n) (GenField k n)))
      else (↑(gam k n (LVar ℕ Empty n))⁻¹ : Matrix (Fin n) (Fin n) _).transpose) I' J = C z := by
    rw [gam_val, gam_inv, ← Matrix.transpose_map]
    split_ifs
    · exact ⟨_, (minorMap _ _ C n (genMat k n)⁻¹ I' J).symm⟩
    · exact ⟨_, (minorMap _ _ C n (genMat k n).transpose I' J).symm⟩
  rw [hz, ← add_zero (sgn last * bc c (μ i m))]
  refine wge_mul (wge_hom (wt_word isVec S (fun j hj => (hS j).2 hj) μ c last m hm' i le_rfl I')
    fun hne => ?_) (wge_C z)
  exact col_bound (hp.2.1 i hi) c last m hm I' (pathWord_card hp c _ i hi I' hne)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
