-- Prove2me | solution 1 for Formalism.BehrendSets.Sums.two_le_cast_of_two_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:43.817861+00:00
-- url     : https://prove2.me/submissions/c09e2b4f-b398-4bd7-892c-9191cc7ba7d4

import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_TwoLeCastOfTwoLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Real
noncomputable section
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Sums
namespace Formalism.BehrendSets.Sums
theorem _root_.solution (M : ℕ) (hM : 2 ≤ M) : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
end Formalism.BehrendSets.Sums
