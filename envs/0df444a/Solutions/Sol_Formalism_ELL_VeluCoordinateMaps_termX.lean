-- Prove2me | solution 1 for Formalism.ELL.VeluCoordinateMaps.termX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:10.742032+00:00
-- url     : https://prove2.me/submissions/cd318876-69c2-47c9-88ef-669dd8aac497

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
theorem _root_.solution (x xQ u Di v uQ : F) (h : (x - xQ)⁻¹ = u ^ 2 * Di) :
    (v / (x - xQ) + uQ / (x - xQ) ^ 2) * u ^ 2 = u ^ 4 * (v * Di + uQ * u ^ 2 * Di ^ 2) := by
  simp only [div_eq_mul_inv, ← inv_pow, h]
  ring
end Formalism.ELL.VeluCoordinateMaps
