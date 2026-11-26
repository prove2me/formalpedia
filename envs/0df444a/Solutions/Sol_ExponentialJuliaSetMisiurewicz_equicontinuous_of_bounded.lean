-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.equicontinuous_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:11.006805+00:00
-- url     : https://prove2.me/submissions/4cc8c347-8177-4fe2-8fe4-74f8273241a7

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Definitions.Def_ExpChaotic_StripGeometry
import Definitions.Def_ExpChaotic_HalfPlane
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_norm_sub_le_of_bounded

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {ι : Type*} {F : ι → ℂ → ℂ} {M ρ : ℝ} {c : ℂ} (hρ : 0 < ρ)
    (hF : ∀ i, DifferentiableOn ℂ (F i) (ball c (2 * ρ)))
    (hb : ∀ i, ∀ w ∈ ball c (2 * ρ), ‖F i w‖ ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ i : ι, ∀ x ∈ ball c ρ, ∀ y ∈ ball c ρ,
      ‖x - y‖ < δ → ‖F i x - F i y‖ < ε := by
  by_cases hne : Nonempty ι
  · obtain ⟨i0⟩ := hne
    have hM : 0 ≤ M :=
      le_trans (norm_nonneg _) (hb i0 c (Metric.mem_ball_self (by linarith)))
    have hpos : 0 < 2 * M / ρ + 1 := by positivity
    refine ⟨ε / (2 * M / ρ + 1), by positivity, ?_⟩
    intro i x hx y hy hxy
    have h1 := norm_sub_le_of_bounded hρ (hF i) (hb i) hx hy
    have h2 : (2 * M / ρ) * ‖x - y‖ < ε := by
      have hcoef : (0 : ℝ) ≤ 2 * M / ρ := by positivity
      have := mul_le_mul_of_nonneg_left (le_of_lt hxy) hcoef
      calc (2 * M / ρ) * ‖x - y‖
          ≤ (2 * M / ρ) * (ε / (2 * M / ρ + 1)) := this
        _ < ε := by
            rw [mul_div_assoc']
            rw [div_lt_iff₀ hpos]
            nlinarith [hε]
    linarith
  · exact ⟨1, one_pos, fun i => absurd ⟨i⟩ hne⟩
end ExponentialJuliaSetMisiurewicz
