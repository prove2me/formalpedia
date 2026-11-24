-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.hol_continuousOn_fderiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:34.221809+00:00
-- url     : https://prove2.me/submissions/a16befaf-d85f-436e-973d-e58dd70e2641

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_hol_hasDerivAt_line
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_hol_radius

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
theorem _root_.solution {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → F} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (v : Fin d → ℂ) : ContinuousOn (fun x => fderiv ℂ g x v) Ω := by
  intro x₀ hx₀
  apply ContinuousAt.continuousWithinAt
  obtain ⟨R, r, hR, hr, hsub, hmem⟩ := hol_radius hΩ hx₀ v
  have hK : IsCompact (Metric.closedBall x₀ R) := isCompact_closedBall x₀ R
  have huc := hK.uniformContinuousOn_of_continuous (hg.continuousOn.mono hsub)
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := huc (ε * r / 2) (by positivity)
  refine ⟨min δ (R / 2), lt_min hδ (by positivity), ?_⟩
  intro x hx
  have hx1 : dist x x₀ < δ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx2 : x ∈ Metric.ball x₀ (R / 2) := lt_of_lt_of_le hx (min_le_right _ _)
  have hx0 : x₀ ∈ Metric.ball x₀ (R / 2) := Metric.mem_ball_self (by positivity)
  have hd : ∀ ζ ∈ Metric.closedBall (0 : ℂ) r,
      HasDerivAt (fun ζ : ℂ => g (x + ζ • v) - g (x₀ + ζ • v))
        (fderiv ℂ g (x + ζ • v) v - fderiv ℂ g (x₀ + ζ • v) v) ζ := fun ζ hζ =>
    (hol_hasDerivAt_line hΩ hg x v ζ (hsub (hmem x hx2 ζ hζ))).sub
      (hol_hasDerivAt_line hΩ hg x₀ v ζ (hsub (hmem x₀ hx0 ζ hζ)))
  have hdc : DiffContOnCl ℂ (fun ζ : ℂ => g (x + ζ • v) - g (x₀ + ζ • v)) (Metric.ball 0 r) := by
    apply DifferentiableOn.diffContOnCl
    intro ζ hζ
    exact (hd ζ (Metric.closure_ball_subset_closedBall hζ)).differentiableAt.differentiableWithinAt
  have hb : ∀ ζ ∈ Metric.sphere (0 : ℂ) r, ‖g (x + ζ • v) - g (x₀ + ζ • v)‖ ≤ ε * r / 2 := by
    intro ζ hζ
    have hζ' := Metric.sphere_subset_closedBall hζ
    rw [← dist_eq_norm]
    apply le_of_lt
    apply hδ' _ (hmem x hx2 ζ hζ') _ (hmem x₀ hx0 ζ hζ')
    simpa using hx1
  have h1 := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdc hb
  have h2 := (hd 0 (Metric.mem_closedBall_self hr.le)).deriv
  rw [h2] at h1
  simp only [zero_smul, add_zero] at h1
  rw [dist_eq_norm]
  calc ‖fderiv ℂ g x v - fderiv ℂ g x₀ v‖ ≤ ε * r / 2 / r := h1
    _ = ε / 2 := by field_simp
    _ < ε := by linarith
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
