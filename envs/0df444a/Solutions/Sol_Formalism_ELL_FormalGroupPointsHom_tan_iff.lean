-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.tan_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:19.960889+00:00
-- url     : https://prove2.me/submissions/f294142a-dccf-482c-a57a-d2d2bf007545

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_tan_x_id
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_tan_y_id

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
    (c / v = W.addX (z / w) (z / w) ((3 * (z / w) ^ 2 + 2 * W.a₂ * (z / w) + W.a₄ - W.a₁ * (-1 / w)) /
      (-1 / w - W.negY (z / w) (-1 / w))) ∧
      -1 / v = W.addY (z / w) (z / w) (-1 / w) ((3 * (z / w) ^ 2 + 2 * W.a₂ * (z / w) + W.a₄
        - W.a₁ * (-1 / w)) / (-1 / w - W.negY (z / w) (-1 / w)))) ↔
    (tanPX W.a₁ W.a₂ W.a₃ W.a₄ z w c v = 0 ∧ tanPY W.a₁ W.a₂ W.a₃ W.a₄ z w c v = 0) := by
  have hk1 : v * w ^ 2 * (-2 + W.a₁ * z + W.a₃ * w) ^ 2 ≠ 0 := by positivity
  have hk2 : v * w ^ 2 * (-2 + W.a₁ * z + W.a₃ * w) ≠ 0 := by positivity
  have eX := tan_x_id W hw hM hv (c := c)
  have eY := tan_y_id W hw hM hv (c := c)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [← eX, h1, sub_self, zero_mul], ?_⟩
    rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, ← h1] at h2
    rw [h2, sub_self, zero_mul] at eY
    exact neg_eq_zero.mp eY.symm
  · rintro ⟨h1, h2⟩
    rw [← eX] at h1
    have h1' := sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hk1)
    refine ⟨h1', ?_⟩
    rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, ← h1']
    rw [h2, neg_zero] at eY
    exact sub_eq_zero.mp ((mul_eq_zero.mp eY).resolve_right hk2)
end Formalism.ELL.FormalGroupPointsHom
