-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_C1_source_small_jump_bound_from_actual_compact_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:57:46.957844+00:00
-- url     : https://prove2.me/submissions/e62ae919-c072-4a57-9c91-934377583b30

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_predictable_small_mark_discounted_L1_by_source_variation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Genuine original BV C1 smoothness on a positive reserve band supplies
the exact small-negative-mark first-variation envelope without a free Lipschitz axiom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC1 : X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (hq : 0 ≤ q) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hSmoothBand : Icc (a / 2) b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0)
    (hK : ∀ y ∈ Icc (a / 2) b, ‖deriv w y‖₊ ≤ K)
    (ω : Ω) (t : ℝ≥0)
    (hBand : Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t ∈ Icc a b)
    (z : ℝ) (hzSmall : -a / 2 ≤ z ∧ z ≤ 0) :
    |Real.exp (-(q * (t : ℝ))) *
      (w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t + z) -
       w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t))| ≤
      (K : ℝ) * |z| := by
  have hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ (K : ℝ) * |u - v| :=
    avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
      X hBV C w hwC1 (a / 2) b hOpen hSmoothBand K hK
  exact avram_wave7_02_original_BV_C1_predictable_small_mark_discounted_L1_by_source_variation
    X x D w q hq a b (K : ℝ) ha hab (NNReal.coe_nonneg K)
    hLip ω t hBand z hzSmall
