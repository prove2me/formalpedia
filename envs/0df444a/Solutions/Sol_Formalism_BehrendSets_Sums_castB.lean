-- Prove2me | solution 1 for Formalism.BehrendSets.Sums.castB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:42.670796+00:00
-- url     : https://prove2.me/submissions/cfae780c-811b-4b85-84ea-a653a7c11db3

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
theorem _root_.solution (M k : ℕ) (hM : 2 ≤ M) :
    (((M * (k + 1) - 1 : ℕ)) : ℝ) = (M : ℝ) * ((k : ℝ) + 1) - 1 := by
  have h : 1 ≤ M * (k + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  rw [Nat.cast_sub h]
  push_cast
  ring
end Formalism.BehrendSets.Sums
