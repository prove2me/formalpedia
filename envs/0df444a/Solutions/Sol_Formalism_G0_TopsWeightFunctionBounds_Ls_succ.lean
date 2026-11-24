-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.Ls_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:43.838798+00:00
-- url     : https://prove2.me/submissions/bd99ecaa-1fc7-45bc-b1b9-0958f75025ab

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
theorem _root_.solution (n : ℕ) (T : Finset ℕ) (b t m : ℕ) :
    Ls n T b t (m + 1) = decide ((b + (t + 1)) % n ∈ T) :: Ls n T b (t + 1) m := by
  unfold Ls
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_apply]
  rw [show t + 1 + (x + 1) = t + 1 + 1 + x by omega]
end Formalism.G0.TopsWeightFunctionBounds
