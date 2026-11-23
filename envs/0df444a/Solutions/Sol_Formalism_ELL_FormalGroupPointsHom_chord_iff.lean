-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.chord_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:16:50.909546+00:00
-- url     : https://prove2.me/submissions/90001509-1cbe-4ed6-9139-ca9b156f7324

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_chord_x_id
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_chord_y_id

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
theorem _root_.solution {z1 z2 w1 w2 c v : E} (hw1 : w1 ≠ 0) (hw2 : w2 ≠ 0)
    (hN : z1 * w2 - z2 * w1 ≠ 0) (hv : v ≠ 0) :
    (c / v = W.addX (z1 / w1) (z2 / w2) ((-1 / w1 - -1 / w2) / (z1 / w1 - z2 / w2)) ∧
      -1 / v = W.addY (z1 / w1) (z2 / w2) (-1 / w1) ((-1 / w1 - -1 / w2) / (z1 / w1 - z2 / w2))) ↔
    (chordPX W.a₁ W.a₂ z1 z2 w1 w2 c v = 0 ∧ chordPY W.a₁ W.a₃ z1 z2 w1 w2 c v = 0) := by
  have hk1 : v * (z1 * w2 - z2 * w1) ^ 2 * w1 * w2 ≠ 0 := by
    have := pow_ne_zero 2 hN; positivity
  have hk2 : v * (z1 * w2 - z2 * w1) * w1 ≠ 0 := by positivity
  have eX := chord_x_id W hw1 hw2 hN hv (c := c)
  have eY := chord_y_id W hw1 hw2 hN hv (c := c)
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
