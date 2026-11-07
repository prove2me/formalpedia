-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_uniform_survival_original_strict_prefix_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:57:30.320538+00:00
-- url     : https://prove2.me/submissions/ab879471-e91f-4fcd-a55d-556d1bebfd35

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_surviving_strict_horizon_source_upper
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_uniform_survival_original_caplinear_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_strict_discounted_cash_real_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual strict cash to T-δ and the surviving original right-payment terminal are bounded by the authentic uniform stopped source. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (C : ℝ≥0∞) (hC : 0 < C) (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (q : ℝ) (hq : 0 < q) (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i,
      (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (n : ℕ) (ω : Ω)
    (hSurvive :
      ENNReal.ofReal T < ruinTime X x D ω) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u n i : ℝ)))
    let source : ℕ → ℝ := fun i =>
      V (x + X.X (u n (i + 1)) ω - rightLimit D (u n i) ω) -
      V (x + X.X (u n i) ω - rightLimit D (u n i) ω)
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - T / ((n : ℝ) + 2)),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) ≤
      w x + (∑ i ∈ Finset.range (n + 1), e i * source i) +
        e (n + 1) * (V (x + X.X S ω - rightLimit D (u n (n + 1)) ω) -
          V (x + X.X (u n (n + 1)) ω -
            rightLimit D (u n (n + 1)) ω)) := by
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have hdenge : (1 : ℝ) ≤ (n : ℝ) + 2 := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith
  have hdelta : T / ((n : ℝ) + 2) ≤ T := by
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg (le_of_lt hT) (sub_nonneg.mpr hdenge)]
  have hs : 0 ≤ T - T / ((n : ℝ) + 2) := by linarith
  have hst : T - T / ((n : ℝ) + 2) ≤ T := by
    have hp : 0 ≤ T / ((n : ℝ) + 2) := le_of_lt (div_pos hT hden)
    linarith
  have hCash := avram_p3_grid3_original_strict_discounted_cash_real_monotone
    X q (le_of_lt hq) x D hD.1.1 ω
    (T - T / ((n : ℝ) + 2)) T hs hst
  have hFull := avram_p3_grid4_uniform_survival_original_caplinear_budget
    X x hx C hC hxc w hw0 hw_cont hw_neg hw_smooth hw_grad
    D hD hjump q hq T hT u huniform n ω hSurvive
  dsimp only at hFull ⊢
  linarith only [hCash, hFull]
