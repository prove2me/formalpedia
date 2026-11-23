-- Prove2me | solution 1 for Formalism.ELL.VeluCoordinateMaps.termY
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:21.933108+00:00
-- url     : https://prove2.me/submissions/0ce84b23-ff17-48bf-bf07-db7e27ef536f

import Definitions.Def_Formalism_EllipticTorsion_VeluIntegralModel
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_VeluUSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.VeluCoordinateMaps
open Formalism.G
variable {F : Type*} [Field F]
namespace Formalism.ELL.VeluCoordinateMaps
theorem _root_.solution (x y xQ yQ u Di Ui v uQ c a1 a3 : F) (h : (x - xQ)⁻¹ = u ^ 2 * Di)
    (hx : x * u ^ 2 = Ui) (hy : y * u ^ 3 = -Ui) :
    (uQ * (2 * y + a1 * x + a3) / (x - xQ) ^ 3 + v * (a1 * (x - xQ) + y - yQ) / (x - xQ) ^ 2
        + c / (x - xQ) ^ 2) * u ^ 3 =
      u ^ 4 * (uQ * (-2 * Ui * u ^ 2 + a1 * Ui * u ^ 3 + a3 * u ^ 5) * Di ^ 3
        + v * (a1 * (Ui - xQ * u ^ 2) * u - Ui - yQ * u ^ 3) * Di ^ 2 + c * u ^ 3 * Di ^ 2) := by
  simp only [div_eq_mul_inv, ← inv_pow, h]
  linear_combination (uQ * Di ^ 3 * a1 * u ^ 7 + v * Di ^ 2 * a1 * u ^ 5) * hx
    + (2 * uQ * Di ^ 3 * u ^ 6 + v * Di ^ 2 * u ^ 4) * hy
end Formalism.ELL.VeluCoordinateMaps
