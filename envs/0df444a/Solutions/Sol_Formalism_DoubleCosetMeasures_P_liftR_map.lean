-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.liftR_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:24:59.836806+00:00
-- url     : https://prove2.me/submissions/8f5aa1ed-f051-4dc2-ab9b-d3f34200e20b

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
theorem _root_.solution (M : Matrix (Fin n) (Fin n) K) (hM : IsInt R M) :
    (liftR R M hM).map R.subtype = M := by
  ext i j
  rfl
end Formalism.DoubleCosetMeasures.P
