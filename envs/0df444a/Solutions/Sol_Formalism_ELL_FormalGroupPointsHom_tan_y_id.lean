-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.tan_y_id
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:51.36408+00:00
-- url     : https://prove2.me/submissions/c64f617f-08ed-4472-93f7-df62268a493e

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_tan_slope

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
theorem _root_.solution {z w c v : E} (hw : w ≠ 0) (hM : -2 + W.a₁ * z + W.a₃ * w ≠ 0) (hv : v ≠ 0) :
    (-1 / v - W.negY (c / v) ((3 * (z / w) ^ 2 + 2 * W.a₂ * (z / w) + W.a₄ - W.a₁ * (-1 / w)) /
      (-1 / w - W.negY (z / w) (-1 / w)) * (c / v - z / w) + -1 / w))
      * (v * w ^ 2 * (-2 + W.a₁ * z + W.a₃ * w)) = - tanPY W.a₁ W.a₂ W.a₃ W.a₄ z w c v := by
  rw [tan_slope W hw hM, WeierstrassCurve.Affine.negY, tanPY]
  generalize 3 * z ^ 2 + 2 * W.a₂ * z * w + W.a₄ * w ^ 2 + W.a₁ * w = Nt
  generalize -2 + W.a₁ * z + W.a₃ * w = M at *
  field_simp
  try ring
end Formalism.ELL.FormalGroupPointsHom
