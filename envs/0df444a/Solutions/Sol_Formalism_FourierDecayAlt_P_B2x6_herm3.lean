-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x6.herm3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:36:28.188678+00:00
-- url     : https://prove2.me/submissions/73ce54e4-b2a4-4b9b-9e7f-0715b79db97e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_iF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_iL_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lv_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_sum3
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_hpk_mulVec
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_tau_out
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_tau_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_iL_val
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_tau_out


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x6
theorem _root_.solution (u w : Fin (2 * (1 + r') + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) u w =
      star (w (iF k r')) * u (iL k r') + star (w (iL k r')) * u (iF k r') + herm (Hpk k r') (res u) (res w) := by
  have tF : WeylGroupFacts.tau k (1 + r') (iF k r') = iL k r' := by
    apply Fin.ext; rw [iL_val, tau_out _ (by rw [iF_val]; omega), iF_val]; omega
  have tL : WeylGroupFacts.tau k (1 + r') (iL k r') = iF k r' := by
    apply Fin.ext; rw [iF_val, tau_out _ (by rw [iL_val]; omega), iL_val]; omega
  have tm : ∀ j, WeylGroupFacts.tau k (1 + r') (lv k r' j) = lv k r' (WeylGroupFacts.tau k r' j) := by
    intro j
    have := j.isLt
    apply Fin.ext; rw [lv_val]
    by_cases hj : j.val < r' ∨ r' + k < j.val
    · rw [tau_out _ hj, tau_out _ (by rw [lv_val]; omega), lv_val]; omega
    · rw [tau_mid _ hj, tau_mid _ (by rw [lv_val]; omega), lv_val]
  have sF : WeylGroupFacts.sgn k (1 + r') (iF k r') = 1 := if_neg (by rw [iF_val]; omega)
  have sL : WeylGroupFacts.sgn k (1 + r') (iL k r') = 1 := if_neg (by rw [iL_val]; omega)
  have sm : ∀ j, WeylGroupFacts.sgn k (1 + r') (lv k r' j) = WeylGroupFacts.sgn k r' j := by
    intro j
    by_cases hj : j.val = r' + k
    · rw [WeylGroupFacts.sgn, WeylGroupFacts.sgn, if_pos hj, if_pos (by rw [lv_val]; omega)]
    · rw [WeylGroupFacts.sgn, WeylGroupFacts.sgn, if_neg hj, if_neg (by rw [lv_val]; omega)]
  simp only [herm, dotProduct, hpk_mulVec, Pi.star_apply]
  rw [sum3]
  simp only [tF, tL, tm, sF, sL, sm, res, one_mul]
  ring
end Formalism.FourierDecayAlt.P.B2x6
