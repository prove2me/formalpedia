-- Prove2me | solution 1 for Formalism.ELL.RootExponentBounds.bmem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:09.894809+00:00
-- url     : https://prove2.me/submissions/1f58c944-a00c-414f-8c53-0edbccacd492

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_ChangeIntegral
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_Change

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ELL Formalism.G
open Formalism Formalism.ELL Formalism.ELL.RootExponentBounds
universe u
namespace Formalism.ELL.RootExponentBounds
theorem _root_.solution {K : Type u} [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K)
    (h1 : W.a₁ ∈ unitBall K) (h2 : W.a₂ ∈ unitBall K) (h3 : W.a₃ ∈ unitBall K)
    (h4 : W.a₄ ∈ unitBall K) (h6 : W.a₆ ∈ unitBall K) :
    W.b₂ ∈ unitBall K ∧ W.b₄ ∈ unitBall K ∧ W.b₆ ∈ unitBall K ∧ W.b₈ ∈ unitBall K := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [WeierstrassCurve.b₂]; (repeat (first
  | assumption | apply ofNatB
  | apply add_mem | apply sub_mem | apply mul_mem | apply pow_mem | apply neg_mem))
  · simp only [WeierstrassCurve.b₄]; (repeat (first
  | assumption | apply ofNatB
  | apply add_mem | apply sub_mem | apply mul_mem | apply pow_mem | apply neg_mem))
  · simp only [WeierstrassCurve.b₆]; (repeat (first
  | assumption | apply ofNatB
  | apply add_mem | apply sub_mem | apply mul_mem | apply pow_mem | apply neg_mem))
  · simp only [WeierstrassCurve.b₈]; (repeat (first
  | assumption | apply ofNatB
  | apply add_mem | apply sub_mem | apply mul_mem | apply pow_mem | apply neg_mem))
end Formalism.ELL.RootExponentBounds
