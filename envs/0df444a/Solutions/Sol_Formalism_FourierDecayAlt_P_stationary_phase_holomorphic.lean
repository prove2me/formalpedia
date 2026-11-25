-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.stationary_phase_holomorphic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:56:44.378495+00:00
-- url     : https://prove2.me/submissions/711fdc06-cbe6-46eb-be24-5a9b558e6b2b

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_isAddHaar_muPi
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_stationary_phase_dim_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_add_update_eq_update_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.StationaryPhase := by
  intro d β hβ r Λ hr hΛ
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨0, ?_⟩
    intro x₀ g dg H _ _ _ _ _ _ V _ _ _ a S _ _ _ t _
    rw [Formalism.FourierDecayAlt.P.StationaryPhaseModel.stationary_phase_dim_zero β x₀ g H a t]
    simp
  obtain ⟨C, -, hC⟩ := Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_zero d hd β hβ r Λ hr hΛ
  refine ⟨C, ?_⟩
  intro x₀ g dg H hg hb hdg hdg0 hH hgrad V _ _ _ a S ha hsupp hS t ht
  have := Formalism.FourierDecayAlt.P.StationaryPhaseModel.isAddHaar_muPi d β hβ
  have hball : ∀ (ρ : ℝ) (x : Fin d → ℂ), x ∈ Metric.ball (0 : Fin d → ℂ) ρ → x₀ + x ∈ Metric.ball x₀ ρ := by
    intro ρ x hx
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  have hcball : ∀ (ρ : ℝ) (x : Fin d → ℂ), x ∈ Metric.closedBall (0 : Fin d → ℂ) ρ →
      x₀ + x ∈ Metric.closedBall x₀ ρ := by
    intro ρ x hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  have key := hC (fun x => g (x₀ + x)) (fun x => dg (x₀ + x)) H
    (by
      refine hg.comp (f := fun x => x₀ + x) ?_ (fun x hx => hball _ x hx)
      exact (differentiable_id.const_add x₀).differentiableOn)
    (fun x hx => hb _ (hball _ x hx))
    (by
      intro x hx k
      have h1 := hdg (x₀ + x) (hball _ x hx) k
      have h2 : HasDerivAt (fun η => g (Function.update (x₀ + x) k η)) (dg (x₀ + x) k) (x₀ k + x k) := h1
      have h3 := h2.comp_const_add (x₀ k) (x k)
      simpa only [Formalism.FourierDecayAlt.P.StationaryPhaseModel.add_update_eq_update_add] using h3)
    (by intro k; simpa using hdg0 k)
    (by
      intro i j
      have h1 := hH i j
      have h2 : HasDerivAt (fun η => dg (Function.update x₀ j η) i) (H i j) (x₀ j + 0) := by simpa using h1
      have h3 := h2.comp_const_add (x₀ j) 0
      have h4 : ∀ ξ : ℂ, x₀ + Function.update (0 : Fin d → ℂ) j ξ = Function.update x₀ j (x₀ j + ξ) := by
        intro ξ
        rw [Formalism.FourierDecayAlt.P.StationaryPhaseModel.add_update_eq_update_add, add_zero]
      simpa only [h4] using h3)
    (by
      intro x hx
      have h1 := hgrad (x₀ + x) (hcball _ x hx)
      simpa using h1)
    V (fun x => a (x₀ + x)) S
    (ha.comp (contDiff_const.add contDiff_id))
    (by
      intro x hx
      have h1 : x₀ + x ∈ Metric.closedBall x₀ r := hsupp hx
      simpa [Metric.mem_closedBall, dist_eq_norm] using h1)
    (by
      intro j hj x
      rw [iteratedFDeriv_comp_add_left]
      exact hS j hj _)
    t ht
  have hint : ∫ x : Fin d → ℂ, Formalism.FourierDecayAlt.G.psi β (g x / t) • a x ∂(Formalism.FourierDecayAlt.G.muPi β (Fin d)) =
      ∫ x : Fin d → ℂ, Formalism.FourierDecayAlt.G.psi β (g (x₀ + x) / t) • a (x₀ + x) ∂(Formalism.FourierDecayAlt.G.muPi β (Fin d)) :=
    (MeasureTheory.integral_add_left_eq_self (μ := Formalism.FourierDecayAlt.G.muPi β (Fin d))
      (fun x => Formalism.FourierDecayAlt.G.psi β (g x / t) • a x) x₀).symm
  rw [hint]
  simpa using key
end Formalism.FourierDecayAlt.P
