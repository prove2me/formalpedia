-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.hol_radius
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:21.90658+00:00
-- url     : https://prove2.me/submissions/c8142480-8bf2-4385-8895-26edf64aa364

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution {Ω : Set (Fin d → ℂ)} (hΩ : IsOpen Ω) {x₀ : Fin d → ℂ} (hx₀ : x₀ ∈ Ω) (v : Fin d → ℂ) :
    ∃ R r : ℝ, 0 < R ∧ 0 < r ∧ Metric.closedBall x₀ R ⊆ Ω ∧
      ∀ x ∈ Metric.ball x₀ (R / 2), ∀ ζ ∈ Metric.closedBall (0 : ℂ) r, x + ζ • v ∈ Metric.closedBall x₀ R := by
  obtain ⟨R, hR, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hx₀)
  refine ⟨R, R / (2 * (‖v‖ + 1)), hR, by positivity, hsub, ?_⟩
  intro x hx ζ hζ
  rw [Metric.mem_ball, dist_eq_norm] at hx
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hζ
  rw [Metric.mem_closedBall, dist_eq_norm]
  have h1 : ‖ζ • v‖ ≤ R / 2 := by
    rw [norm_smul]
    calc ‖ζ‖ * ‖v‖ ≤ R / (2 * (‖v‖ + 1)) * (‖v‖ + 1) := by
          apply mul_le_mul hζ (by linarith) (norm_nonneg _) (by positivity)
      _ = R / 2 := by field_simp
  calc ‖x + ζ • v - x₀‖ = ‖(x - x₀) + ζ • v‖ := by congr 1; abel
    _ ≤ ‖x - x₀‖ + ‖ζ • v‖ := norm_add_le _ _
    _ ≤ R := by linarith
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
