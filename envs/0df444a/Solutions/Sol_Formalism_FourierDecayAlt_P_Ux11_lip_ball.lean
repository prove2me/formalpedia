-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux11.lip_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:27:12.871244+00:00
-- url     : https://prove2.me/submissions/2c9d4b39-f113-440a-850f-d8bde2084b8d

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakToStrongSmoothnessReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux11
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.Ux11
theorem _root_.solution {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : X → F} {x₀ : X} {r M : ℝ}
    (hd : ∀ y ∈ Metric.ball x₀ r, DifferentiableAt ℝ f y)
    (hb : ∀ y ∈ Metric.ball x₀ r, ‖fderiv ℝ f y‖ ≤ M) {y : X} (hy : y ∈ Metric.ball x₀ r) :
    ‖f y - f x₀‖ ≤ M * ‖y - x₀‖ :=
  (convex_ball x₀ r).norm_image_sub_le_of_norm_fderiv_le hd hb
    (Metric.mem_ball_self (lt_of_le_of_lt dist_nonneg hy)) hy
end Formalism.FourierDecayAlt.P.Ux11
