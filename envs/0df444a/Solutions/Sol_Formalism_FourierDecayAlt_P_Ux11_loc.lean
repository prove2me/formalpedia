-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux11.loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:27:10.977748+00:00
-- url     : https://prove2.me/submissions/f7ccf28a-af37-47e3-83f7-33be54a514fa

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
theorem _root_.solution {Ω : Set X} {bd : X → ℝ} (hΩ : IsOpen Ω) (hbd : ContinuousOn bd Ω) {x₀ : X} (hx : x₀ ∈ Ω) :
    ∃ r > 0, ∀ y ∈ Metric.ball x₀ r, y ∈ Ω ∧ bd y ≤ bd x₀ + 1 := by
  have h2 : ∀ᶠ y in 𝓝 x₀, bd y ∈ Iic (bd x₀ + 1) :=
    Filter.Tendsto.eventually (hbd.continuousAt (hΩ.mem_nhds hx)) (Iic_mem_nhds (lt_add_one _))
  have h1 : ∀ᶠ y in 𝓝 x₀, y ∈ Ω ∧ bd y ≤ bd x₀ + 1 := Filter.Eventually.and (hΩ.mem_nhds hx) h2
  exact Metric.eventually_nhds_iff_ball.1 h1
end Formalism.FourierDecayAlt.P.Ux11
