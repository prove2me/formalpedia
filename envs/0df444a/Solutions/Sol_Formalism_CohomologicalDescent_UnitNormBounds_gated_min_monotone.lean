-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.gated_min_monotone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:03:41.095785+00:00
-- url     : https://prove2.me/submissions/72ca0106-6352-4542-b278-93b58825bfad

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.UnitNormBounds
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
namespace Formalism.CohomologicalDescent.UnitNormBounds
theorem _root_.solution (l k t : ℕ) (D : ℤ) {a b : ℝ} (hab : a ≤ b) :
    (if ((d0 l D : ℕ) : ℤ) < D then min (min (k : ℝ) (t : ℝ)) (a / (d0 l D : ℝ)) else 0) ≤
      (if ((d0 l D : ℕ) : ℤ) < D then min (min (k : ℝ) (t : ℝ)) (b / (d0 l D : ℝ)) else 0) := by
  split_ifs
  · exact min_le_min_left _ (div_le_div_of_nonneg_right hab (Nat.cast_nonneg _))
  · exact le_rfl
end Formalism.CohomologicalDescent.UnitNormBounds
