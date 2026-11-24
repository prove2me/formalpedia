-- Prove2me | solution 1 for Formalism.CohomologicalDescent.sums_le_of_gate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:45:43.21606+00:00
-- url     : https://prove2.me/submissions/1b8e157a-30f5-4ce3-8a75-d170fe1c47c0

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Theorems.Thm_Formalism_CohomologicalDescent_leastCongruentPos_mem_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent
open Classical
namespace Formalism.CohomologicalDescent
theorem _root_.solution (l D : ℕ) (hD : 1 ≤ D) (hg : ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ)) :
    (l : ℤ) ≤ (D : ℤ) - (d0 l (D : ℤ) : ℤ) := by
  obtain ⟨_, hdvd, _⟩ := leastCongruentPos_mem_le l D hD
  exact Int.le_of_dvd (by omega) hdvd
end Formalism.CohomologicalDescent
