-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.even_mod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:30.251824+00:00
-- url     : https://prove2.me/submissions/d159e6a7-9ed7-4cd0-96fd-6b80b43ed908

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
namespace Formalism.G0.TopsWeightFunctionBounds
theorem _root_.solution {n : ℕ} (hn : Even n) (x : ℕ) : Even (x % n) ↔ Even x := by
  rw [Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ (even_iff_two_dvd.1 hn)]
end Formalism.G0.TopsWeightFunctionBounds
