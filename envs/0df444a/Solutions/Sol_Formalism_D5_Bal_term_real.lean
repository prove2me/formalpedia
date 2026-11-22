-- Prove2me | solution 1 for Formalism.D5.Bal.term_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:51:35.17589+00:00
-- url     : https://prove2.me/submissions/913a63a2-7894-4133-b2da-96352e619e11

import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
open Formalism.D5.Bal
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.D5.Bal
theorem _root_.solution (a w : ℝ) (hw : w ≠ 0) (n : ℕ) : a / n - w = w * (a / w / n - 1) := by
  rw [mul_sub, mul_one, div_div, mul_div_assoc', mul_div_mul_left _ _ hw]
end Formalism.D5.Bal
