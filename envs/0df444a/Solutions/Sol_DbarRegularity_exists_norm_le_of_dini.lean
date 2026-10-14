-- Prove2me | solution 1 for DbarRegularity.exists_norm_le_of_dini
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T19:24:22.157041+00:00
-- url     : https://prove2.me/submissions/42d0ca28-924b-484f-9ece-ef83320fef15

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.ProperSpace
import Theorems.Thm_DbarRegularity_continuousOn_compl_zero_of_dini



namespace DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

/-- A function `Ω` on `ℝ^d`, homogeneous of degree `0`, whose spherical modulus of continuity
satisfies the Dini condition `∫₀¹ w(δ) / δ dδ < ∞`, is bounded. -/
theorem exists_norm_le_of_dini {d : ℕ} (Ω : EuclideanSpace ℝ (Fin d) → ℂ)
    (hhom : ∀ x, ∀ t : ℝ, 0 < t → Ω (t • x) = Ω x)
    (hdini : ∫⁻ δ in Set.Ioc (0 : ℝ) 1,
      (⨆ (x : EuclideanSpace ℝ (Fin d)) (x' : EuclideanSpace ℝ (Fin d)) (_ : ‖x‖ = 1)
        (_ : ‖x'‖ = 1) (_ : ‖x - x'‖ ≤ δ), ‖Ω x - Ω x'‖ₑ) / ENNReal.ofReal δ < ⊤) :
    ∃ M : ℝ, ∀ x, ‖Ω x‖ ≤ M := by
  have hc := continuousOn_compl_zero_of_dini Ω hhom hdini
  have hsub : sphere (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ {0}ᶜ := by
    intro x hx h0
    rw [mem_singleton_iff.mp h0, mem_sphere_zero_iff_norm, norm_zero] at hx
    exact zero_ne_one hx
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin d)) 1).exists_bound_of_continuousOn
    (hc.mono hsub)
  refine ⟨max C ‖Ω 0‖, fun x => ?_⟩
  by_cases hx : x = 0
  · rw [hx]; exact le_max_right _ _
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hmem : ‖x‖⁻¹ • x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hx0.ne'
  rw [← hhom x _ (inv_pos.mpr hx0)]
  exact (hC _ hmem).trans (le_max_left _ _)

end DbarRegularity

open DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

theorem solution {d : ℕ} (Ω : EuclideanSpace ℝ (Fin d) → ℂ)
    (hhom : ∀ x, ∀ t : ℝ, 0 < t → Ω (t • x) = Ω x)
    (hdini : ∫⁻ δ in Set.Ioc (0 : ℝ) 1,
      (⨆ (x : EuclideanSpace ℝ (Fin d)) (x' : EuclideanSpace ℝ (Fin d)) (_ : ‖x‖ = 1)
        (_ : ‖x'‖ = 1) (_ : ‖x - x'‖ ≤ δ), ‖Ω x - Ω x'‖ₑ) / ENNReal.ofReal δ < ⊤) :
    ∃ M : ℝ, ∀ x, ‖Ω x‖ ≤ M :=
  exists_norm_le_of_dini Ω hhom hdini
