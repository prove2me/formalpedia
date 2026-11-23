-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_ordL_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:43.248828+00:00
-- url     : https://prove2.me/submissions/340cc6e1-a0e8-4b16-a377-a04c81ecdcd9

import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace Formalism.UG.P
theorem _root_.solution (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) :
    ordL (x * y) = ordL x + ordL y := by
  have hx' : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  have hxy' : Valued.v (x * y) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hx' hy'
  unfold Formalism.UG.ordL
  rw [dif_neg hxy', dif_neg hx', dif_neg hy']
  have key : WithZero.unzero hxy' = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    simp only [WithZero.coe_mul, WithZero.coe_unzero, map_mul]
  rw [key, toAdd_mul]
  ring
end Formalism.UG.P
