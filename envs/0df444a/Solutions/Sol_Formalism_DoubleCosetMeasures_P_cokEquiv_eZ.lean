-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.cokEquiv_eZ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:56:51.793872+00:00
-- url     : https://prove2.me/submissions/1cd235dd-856b-431c-bf07-87d57ca71425

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_coeLin_injective
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_lowUni_mulVec_eLast
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_cokEquiv_mk

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
    (hA : (A.map R.subtype).det = 1) (hB : (B.map R.subtype).det = 1)
    (hlow : IsLowUni (A.map R.subtype)) :
    cokEquiv R A B Z hA hB (eZ R Z) = eZ R (A.map R.subtype * Z * B.map R.subtype) := by
  show cokEquiv R A B Z hA hB (Submodule.Quotient.mk (eLast R)) = Submodule.Quotient.mk (eLast R)
  rw [cokEquiv_mk]
  exact congrArg Submodule.Quotient.mk
    (coeLin_injective R (by rw [coeLin_mulVec]; exact lowUni_mulVec_eLast R hlow))
end Formalism.DoubleCosetMeasures.P
