-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.theta_congruence_padic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:40:14.060234+00:00
-- url     : https://prove2.me/submissions/7876fb07-f6f5-4d25-bcf0-cd6652f69cf8

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_zpow_congruence_general

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution : ThetaCongPadic := by
  intro l _ u c m hu
  obtain ⟨e, he⟩ := zpow_congruence_general ℤ_[l] (l : ℤ_[l]) c u (-m) hu
  refine ⟨e, ?_⟩
  have : ((u ^ (-m) : ℤ_[l]ˣ) : ℤ_[l]) = (1 + ((-m : ℤ) : ℤ_[l]) * ((l : ℤ_[l]) * c)) + (l : ℤ_[l]) ^ 2 * e := by
    linear_combination he
  rw [this]; push_cast; ring
end Formalism.CohomologicalDescent.HeightDescentMinors
