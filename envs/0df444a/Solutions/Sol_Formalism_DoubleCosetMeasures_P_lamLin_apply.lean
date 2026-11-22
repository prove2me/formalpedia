-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.lamLin_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:30:14.321805+00:00
-- url     : https://prove2.me/submissions/7bb39c2e-243a-45eb-a902-b574c4755c46

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
theorem _root_.solution (Z : Matrix (Fin n) (Fin n) K) (v : Fin n → R) :
    lamLin R Z v = Submodule.mkQ _ (lastCoord R (Z⁻¹ *ᵥ coeLin R v)) := rfl
end Formalism.DoubleCosetMeasures.P
