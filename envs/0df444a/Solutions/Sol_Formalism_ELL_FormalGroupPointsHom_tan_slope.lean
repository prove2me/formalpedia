-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.tan_slope
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:28:22.562812+00:00
-- url     : https://prove2.me/submissions/4bc3b7c8-136c-4ae7-81fb-6296cbaf29b3

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef

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
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsHom
open Formalism.ELL Formalism.G
variable {E : Type*} [Field E] (W : WeierstrassCurve.Affine E)
namespace Formalism.ELL.FormalGroupPointsHom
theorem _root_.solution {z w : E} (hw : w ≠ 0) (hM : -2 + W.a₁ * z + W.a₃ * w ≠ 0) :
    (3 * (z / w) ^ 2 + 2 * W.a₂ * (z / w) + W.a₄ - W.a₁ * (-1 / w)) /
      (-1 / w - W.negY (z / w) (-1 / w)) =
    (3 * z ^ 2 + 2 * W.a₂ * z * w + W.a₄ * w ^ 2 + W.a₁ * w) / (w * (-2 + W.a₁ * z + W.a₃ * w)) := by
  have h : -1 / w - W.negY (z / w) (-1 / w) = (-2 + W.a₁ * z + W.a₃ * w) / w := by
    rw [WeierstrassCurve.Affine.negY]; field_simp; ring
  rw [h]
  field_simp
  ring
end Formalism.ELL.FormalGroupPointsHom
