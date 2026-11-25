-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qn_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:46:47.243681+00:00
-- url     : https://prove2.me/submissions/370d28b7-aa93-4c61-8b5f-5405e886fc61

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_rowNu
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_eval_eq_coeff
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_colHom
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylRowGraded
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwLine
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwRowWeight
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehw_eval_idFrame_hw
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehw_kill


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) (ν : Fin n → ℕ) (hν : Antitone ν) (F : MvPolynomial (Fin n × Fin n) ℚ)
    (hF : F ∈ dualWeyl ℚ n n ν) :
    weightedHomogeneousComponent (rowW n n) ν F = eval (idFrame ℚ n n) F • hw ℚ (le_refl n) ν := by
  classical
  set G := weightedHomogeneousComponent (rowW n n) ν F with hGdef
  have hG : G ∈ dualWeyl ℚ n n ν := dualWeylRowGraded ℚ n n ν _ F hF
  have hGh : IsWeightedHomogeneous (rowW n n) G (rowNu (r := n) ν) := by
    rw [qn_rowNu]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  obtain ⟨c, hc⟩ := hwLine ℚ n n (le_refl n) ν hν G hG
    (fun a b hab k hk => lehw_kill (le_refl n) ν hν G hG hGh a b hab k hk)
  have hHW := hwRowWeight ℚ n n (le_refl n) ν hν
  rw [qn_rowNu] at hHW
  have hH1 : coeff (lhwline_mnu (le_refl n) ν) (hw ℚ (le_refl n) ν) = 1 := by
    rw [← qn_eval_eq_coeff n ν _ (qn_colHom ℚ n ν _ (hwMem ℚ n n (le_refl n) ν hν))]
    exact lehw_eval_idFrame_hw (le_refl n) ν
  have hwt : Finsupp.weight (rowW n n) (lhwline_mnu (le_refl n) ν) = ν :=
    hHW (by rw [hH1]; exact one_ne_zero)
  have h1 : coeff (lhwline_mnu (le_refl n) ν) F = c := by
    have e : coeff (lhwline_mnu (le_refl n) ν) F = coeff (lhwline_mnu (le_refl n) ν) G := by
      rw [hGdef, coeff_weightedHomogeneousComponent, if_pos hwt]
    rw [e, hc, coeff_smul, hH1, smul_eq_mul, mul_one]
  rw [qn_eval_eq_coeff n ν F (qn_colHom ℚ n ν F hF), h1, hc]
end Formalism.InvariantFactorPaths.ColumnFamilies
