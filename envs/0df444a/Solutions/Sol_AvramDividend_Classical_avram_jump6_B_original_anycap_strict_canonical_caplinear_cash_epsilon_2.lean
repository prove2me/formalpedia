-- Prove2me | solution 2 for AvramDividend.Classical.avram_jump6_B_original_anycap_strict_canonical_caplinear_cash_epsilon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:07:10.2465+00:00
-- url     : https://prove2.me/submissions/5601e71f-81e3-42f8-ba7b-191ce916b1d2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anycap_strict_each_grid_caplinear_signed_cash
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_discount_error_finite_and_vanishing
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
    (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      V y = if y ≤ C.toReal then w y else w C.toReal + (y - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (hStrict : (t : ℝ≥0∞) < ruinTime X x D ω)
    (n : ℕ) (ht : t ≤ (n : ℝ≥0)) :
    let v : ℕ → ℕ → ℝ≥0 := fun j i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    let m : ℕ → ℕ := fun j => (n + 1) * (j + 1)
    let Cash : ℝ≥0∞ :=
      ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (t : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in (atTop : Filter ℕ),
      Cash.toReal + (V (x - rightLimit D 0 ω) - V x) -
        (∑ i ∈ Finset.range (m j),
          Real.exp (-(q * (v j (i + 1) : ℝ))) *
          (V (x + X.X (v j (i + 1)) ω - rightLimit D (v j i) ω) -
            V (x + X.X (v j (i + 1)) ω - rightLimit D (v j (i + 1)) ω)))
        ≤ ε := by
  dsimp
  intro eps heps
  have hgrid :=
    AvramDividend.Classical.avram_jump6_B_original_anycap_strict_each_grid_caplinear_signed_cash
      X x C hC q hq w V hw_cont hw_smooth hw_grad
      hVtop hVfinite D hD ω t hStrict n ht
  have hlim :=
    (AvramDividend.Classical.avram_jump6_B_original_canonical_discount_error_finite_and_vanishing
      D hD.1.1 ω t q hq).2
  have hevent :
      ∀ᶠ j in (atTop : Filter ℕ),
        (ENNReal.ofReal (q * ((1 : ℝ) / (((j : ℕ) : ℝ) + 1))) *
          dividendMeasure D ω (Ioc (0 : ℝ) (t : ℝ))).toReal < eps :=
    by
    simpa only [mem_Iio] using
      hlim.eventually (isOpen_Iio.mem_nhds heps)
  filter_upwards [hevent] with j hj
  exact le_trans (hgrid j) (le_of_lt hj)
