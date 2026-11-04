-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_discounted_c1_strict_interior_stopped_residual_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:56:28.003436+00:00
-- url     : https://prove2.me/submissions/73560155-b536-4337-8e61-64276a97a579

import Mathlib
import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_measurable_stopped_support_residual_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original continuous BV remainder has nonpositive discounted C¹
contribution on a random stopped support entirely in the HJB interior. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (U : ℝ≥0 → Ω → ℝ) (q : ℝ) (C : ℝ≥0∞)
    (S : Ω → Set ℝ≥0) (hS : ∀ ω, MeasurableSet (S ω))
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hInterior : ∀ᵐ ω ∂P, ∀ t ∈ S ω,
      0 < U t ω ∧ ENNReal.ofReal (U t ω) < C) :
    ∀ᵐ ω ∂P, ∃ μ : Measure ℝ≥0,
      (∀ a b : ℝ≥0, a ≤ b →
        μ (Ioc a b) = ENNReal.ofReal (
          ((((b : ℝ) * X.drift - X.X b ω) -
            (∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) -
          (((a : ℝ) * X.drift - X.X a ω) -
            (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))))) ∧
      (∀ a : ℝ≥0, μ {a} = 0) ∧
      (∀ a b : ℝ≥0, a ≤ b → μ (Ioc a b) < ∞) ∧
      -(∫ t in S ω,
        Real.exp (-q * (t : ℝ)) * deriv w (U t ω) ∂μ) ≤ 0 := by
  filter_upwards
    [avram_p3_a_bvdrift_original_measurable_stopped_support_residual_budget X hBV,
      hInterior] with ω hμ hInteriorω
  obtain ⟨μ, hinterval, hatom, hlocal, hbudget⟩ := hμ
  refine ⟨μ, hinterval, hatom, hlocal, ?_⟩
  apply hbudget (S ω) (hS ω)
    (fun t => Real.exp (-q * (t : ℝ)) * deriv w (U t ω))
  intro t ht
  obtain ⟨hpos, hcap⟩ := hInteriorω t ht
  have hgrad : 0 ≤ deriv w (U t ω) :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (hw_grad (U t ω) hpos hcap)
  exact mul_nonneg (le_of_lt (Real.exp_pos _)) hgrad
