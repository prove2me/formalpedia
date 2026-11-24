-- Prove2me | solution 1 for Formalism.UG.P.spherical_ordV_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:35.905913+00:00
-- url     : https://prove2.me/submissions/5a5ae81f-cf5c-49dc-8e96-1b7e212a14e4

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SphericalA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.UG
open Formalism Formalism.UG Formalism.UG.P
variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace Formalism.UG.P
theorem _root_.solution (x y : v.adicCompletion F)
    (hx : x ≠ 0) (hy : y ≠ 0) : ordV F v (x * y) = ordV F v x + ordV F v y := by
  unfold ordV
  have hx' : Valued.v x ≠ 0 := by simpa using hx
  have hy' : Valued.v y ≠ 0 := by simpa using hy
  have hxy : Valued.v (x * y) ≠ 0 := by simpa using mul_ne_zero hx hy
  rw [dif_neg hx', dif_neg hy', dif_neg hxy]
  have : WithZero.unzero hxy = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective; simp [WithZero.coe_unzero, map_mul]
  rw [this, toAdd_mul]; ring
end Formalism.UG.P
