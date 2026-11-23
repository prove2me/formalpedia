-- Prove2me | solution 1 for Formalism.L2.Th1.A.chordFormula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:10.217834+00:00
-- url     : https://prove2.me/submissions/0224eefa-2856-4b37-936b-0cc2bcac6654

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply

set_option autoImplicit false
universe u
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
namespace Formalism.L2.Th1.A
theorem _root_.solution : ChordRegular.{u} := by
  intro A _ W x y xP yP t h1 h2 ht
  rw [WeierstrassCurve.Affine.equation_iff] at h1 h2
  have hX : W.toAffine.addX x xP ((y - yP) * t) = xP +
      ((W.a₄ - W.a₁ * yP + 2 * W.a₂ * xP + 3 * xP ^ 2) * x - (2 * yP + W.a₁ * xP + W.a₃) * y
        + (2 * W.a₆ + W.a₄ * xP - W.a₃ * yP - xP ^ 3)) * t ^ 2 := by
    simp only [WeierstrassCurve.Affine.addX]
    linear_combination t ^ 2 * h1 + t ^ 2 * h2
      - (W.a₁ * (y - yP) * t - (W.a₂ + x + 2 * xP) * (1 + t * (x - xP))) * ht
  refine ⟨hX, ?_⟩
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY]
  linear_combination (y - yP) * ht
end Formalism.L2.Th1.A
