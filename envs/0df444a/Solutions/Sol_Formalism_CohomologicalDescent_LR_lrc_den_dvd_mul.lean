-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrc_den_dvd_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:38:08.483265+00:00
-- url     : https://prove2.me/submissions/1cd04b95-8b5e-4027-9535-262bfbafa5d5

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrcFockZeroRight

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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution (x : ℚ) (m : ℕ) (h : x.den ∣ m) : ∃ z : ℤ, (m : ℚ) * x = z := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨(k : ℤ) * x.num, ?_⟩
  have := Rat.den_mul_eq_num x
  push_cast
  rw [← this]
  ring
end Formalism.CohomologicalDescent.LR
