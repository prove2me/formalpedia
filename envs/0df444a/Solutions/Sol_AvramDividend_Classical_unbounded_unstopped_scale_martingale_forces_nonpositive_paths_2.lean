-- Prove2me | solution 2 for AvramDividend.Classical.unbounded_unstopped_scale_martingale_forces_nonpositive_paths
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:19:57.700369+00:00
-- url     : https://prove2.me/submissions/0a58257f-c843-4863-a534-b2d783cc2f11

import Theorems.Thm_AvramDividend_Classical_nonnegative_zero_initial_martingale_vanishes_ae
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Probability.Martingale.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal

/-- An un-stopped discounted unbounded-variation scale martingale at zero
would rule out all positive increments at every fixed time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    [SigmaFiniteFiltration P 𝓕]
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) (hW0 : W 0 = 0)
    (hStart : ∀ᵐ ω ∂P, X.X 0 ω = 0)
    (hMart : Martingale
      (fun t : ℝ≥0 => fun ω : Ω =>
        Real.exp (-(q * (t : ℝ))) * W (X.X t ω)) 𝓕 P) :
    ∀ t : ℝ≥0, ∀ᵐ ω ∂P, X.X t ω ≤ 0 := by
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (-(q * (t : ℝ))) * W (X.X t ω)
  have hnonneg (t : ℝ≥0) : 0 ≤ᵐ[P] M t :=
    Filter.Eventually.of_forall (fun ω => by
      have hz : 0 ≤ W (X.X t ω) := by
        by_cases hneg : X.X t ω < 0
        · rw [hW.1 _ hneg]
        · exact hW.2.1 _ (le_of_not_gt hneg)
      exact mul_nonneg (le_of_lt (Real.exp_pos _)) hz)
  have hMzero : M 0 =ᵐ[P] (fun _ => (0 : ℝ)) := by
    filter_upwards [hStart] with ω hω
    simp [M, hω, hW0]
  have hMzeroAll :=
    nonnegative_zero_initial_martingale_vanishes_ae
      M hMart hnonneg hMzero
  have hpositive : ∀ y : ℝ, 0 < y → 0 < W y :=
    scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv
  intro t
  filter_upwards [hMzeroAll t] with ω hreward
  by_contra hnot
  have hy : 0 < X.X t ω := lt_of_not_ge hnot
  have hwpos : 0 < W (X.X t ω) := hpositive _ hy
  have hproduct : Real.exp (-(q * (t : ℝ))) * W (X.X t ω) = 0 :=
    hreward
  have hwzero : W (X.X t ω) = 0 :=
    (mul_eq_zero.mp hproduct).resolve_left
      (ne_of_gt (Real.exp_pos _))
  rw [hwzero] at hwpos
  exact (lt_irrefl (0 : ℝ)) hwpos
