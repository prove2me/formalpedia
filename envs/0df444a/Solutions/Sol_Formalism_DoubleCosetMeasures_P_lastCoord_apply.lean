-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.lastCoord_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:30:18.676122+00:00
-- url     : https://prove2.me/submissions/344ed2b9-c3d4-41a4-9d18-6acb2f4f69e0

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution (w : Fin n → K) :
    lastCoord R w = ∑ j : Fin n, if j.val + 1 = n then w j else 0 := by
  unfold lastCoord
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> rfl
end Formalism.DoubleCosetMeasures.P
