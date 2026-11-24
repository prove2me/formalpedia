-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.divided_power_det_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:20:38.420979+00:00
-- url     : https://prove2.me/submissions/4b5aec42-bc60-4a08-903a-afa1cef4ca14

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LA_divided_power_det_mul_of_ne
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {r : ℕ} (a b : Fin r) (hab : a ≠ b) (k n : ℕ) (f : MvPolynomial (Fin r × Fin r) ℤ) :
    rowDiv ℤ a b k (genericDet ℤ r ^ n * f) = genericDet ℤ r ^ n * rowDiv ℤ a b k f := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, divided_power_det_mul_of_ne ℤ a b hab, ih, mul_assoc]
end Formalism.CohomologicalDescent.LD
