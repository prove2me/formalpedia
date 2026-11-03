-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_zero_or_strict_preruin_paymentTimes_clipped_full_stieltjes_grid_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T10:45:36.466513+00:00
-- url     : https://prove2.me/submissions/9160b7e6-fb50-4511-948d-cf045a388df0

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_actual_clipped_preruin_closed_stieltjes_grid_budget_with_initial_atom
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_random_clock_paymentTimes_eq_Icc
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
/-- The original stopped paymentTimes complete cash budget with the
    zero-clock/immediate-ruin atom retained; positive ruin crossing excluded. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (τ : Ω → ℝ≥0) (T : ℝ≥0)
    (hτT : τ ω ≤ T)
    (hPre : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω)
    (u : ℕ → ℕ → ℝ≥0) (hu : ∀ n, Monotone (u n))
    (k : ℕ → ℕ) (hzero : ∀ n, u n 0 = 0)
    (hcover : ∀ n, τ ω ≤ u n (k n))
    (mesh : ℕ → ℝ) (hm : ∀ n, 0 ≤ mesh n)
    (hmesh : ∀ n i, i < k n →
      ((u n (i + 1) : ℝ) - (u n i : ℝ)) ≤ mesh n)
    (hmesh0 : Tendsto mesh atTop (𝓝 0)) :
    (let v : ℕ → ℕ → ℝ≥0 := fun n i => min (u n i) (τ ω)
     (∀ n,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (rightLimit D 0 ω) * ENNReal.ofReal (Real.exp (-(q * 0))) +
      ((∑ i ∈ Finset.range (k n),
        ENNReal.ofReal (Real.exp (-(q * (v n (i + 1) : ℝ)))) *
          ENNReal.ofReal
            (V (x + X.X (v n (i + 1)) ω - rightLimit D (v n i) ω) -
             V (x + X.X (v n (i + 1)) ω - rightLimit D (v n (i + 1)) ω))) +
        ENNReal.ofReal (q * mesh n) *
          dividendMeasure D ω (Ioc (0 : ℝ) (τ ω : ℝ)))) ∧
     Tendsto
       (fun n =>
         (ENNReal.ofReal (q * mesh n) *
          dividendMeasure D ω (Ioc (0 : ℝ) (τ ω : ℝ))).toReal)
       atTop (𝓝 0)) := by
  have hDomain :=
    avram_wave6_06_original_zero_or_strict_preruin_random_clock_paymentTimes_eq_Icc
      X x D ω τ hPre
  have hClosed :=
    avram_wave6_06_actual_clipped_preruin_closed_stieltjes_grid_budget_with_initial_atom
      X x C hC q hq w V hw_cont hw_smooth hw_grad
      hVtop hVfinite D hD ω τ T hτT hPre u hu k hzero hcover mesh hm hmesh hmesh0
  simpa only [hDomain] using hClosed
