-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.cokEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:49:57.947228+00:00
-- url     : https://prove2.me/submissions/59af5426-717c-486d-ae29-7c424ccbd3a2

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
theorem _root_.solution (A B : Matrix (Fin n) (Fin n) R) (Z : Matrix (Fin n) (Fin n) K)
    (hA : (A.map R.subtype).det = 1) (hB : (B.map R.subtype).det = 1) (v : Fin n → R) :
    cokEquiv R A B Z hA hB (Submodule.Quotient.mk v) = Submodule.Quotient.mk (A *ᵥ v) := rfl
end Formalism.DoubleCosetMeasures.P
