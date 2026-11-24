-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.Lst_nodup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:08.5408+00:00
-- url     : https://prove2.me/submissions/403f4e1f-ce9e-42c1-b4c5-21627cbb1add

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_mod_inj

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
theorem _root_.solution (n i : ℕ) : (Lst n i).Nodup := by
  unfold Lst
  apply List.Nodup.map_on _ List.nodup_range
  intro x hx y hy h
  rw [List.mem_range] at hx hy
  have : x + 1 = y + 1 := mod_inj (n := n) (i := i) (x := x + 1) (y := y + 1) (by omega) (by omega) (by simpa [add_assoc] using h)
  omega
end Formalism.G0.TopsWeightFunctionBounds
