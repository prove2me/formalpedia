-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.mod_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:24.056469+00:00
-- url     : https://prove2.me/submissions/8cd9dbfe-3d4d-4aee-812d-c959f95ddc89

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
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
variable {R L₂ : ℕ} {δ : ℝ}
namespace Formalism.G0.TopsWeightFunctionBounds
theorem _root_.solution {n i x y : ℕ} (hx : x < n) (hy : y < n) (h : (i + x) % n = (i + y) % n) : x = y := by
  have h' : x % n = y % n := Nat.ModEq.add_left_cancel' i h
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h'
end Formalism.G0.TopsWeightFunctionBounds
