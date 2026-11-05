-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_compact_band_paid_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:21:21.524898+00:00
-- url     : https://prove2.me/submissions/65690ab8-f655-4663-b968-f4facc6a2a57

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_ubv_C2_interior_band_secant_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_countable_rightjump_local_secant_summable
import Theorems.Thm_avram_p4_f_assembly_original_compact_band_paid_resid_pointwise_upper_bound_a9c704b6
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original paid right-jump residuals are summable and nonpositive on an
honestly localised interior band, using the source C² derivative bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (C : ℝ≥0∞)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0)
    (hDeriv : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K)
    (hjump : ∀ ω (u : ℝ≥0),
      (u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D u ω - D u ω ≤
        w (riskProcess X x D u ω) -
          w (riskProcess X x D u ω -
            (rightLimit D u ω - D u ω)))
    {ι : Type*} (t : ι → ℝ≥0) (ω : Ω)
    (hPre : ∀ i : ι, t i = 0 ∨
      (t i : ℝ≥0∞) < ruinTime X x D ω)
    (hPreBand : ∀ i : ι,
      riskProcess X x D (t i) ω ∈ Icc a b)
    (hPostBand : ∀ i : ι,
      x + X.X (t i) ω - rightLimit D (t i) ω ∈ Icc a b)
    (hPayNonneg : ∀ i : ι,
      0 ≤ rightLimit D (t i) ω - D (t i) ω)
    (hPaySummable : Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) *
        (rightLimit D (t i) ω - D (t i) ω))) :
    Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) *
        ((rightLimit D (t i) ω - D (t i) ω) +
          w (x + X.X (t i) ω - rightLimit D (t i) ω) -
          w (riskProcess X x D (t i) ω))) ∧
    (∑' i : ι, Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))) ≤ 0 := by
  have hLip :=
    avram_p4_d_dividend_ubv_C2_interior_band_secant_lipschitz
      C w hwC2 a b hOpen hBand K hDeriv
  have hLocal : ∀ i : ι,
      w (riskProcess X x D (t i) ω) -
        w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
      max 1 (K : ℝ) * (rightLimit D (t i) ω - D (t i) ω) := avram_p4_f_assembly_original_compact_band_paid_resid_pointwise_upper_bound_a9c704b6 (Ω := Ω) (mΩ := mΩ) (P := P) (𝓕 := 𝓕) (X := X) (x := x) (D := D) (w := w) (q := q) (C := C) (hwC2 := hwC2) (a := a) (b := b) (hOpen := hOpen) (hBand := hBand) (K := K) (hDeriv := hDeriv) (hjump := hjump) (ι := ι) (t := t) (ω := ω) (hPre := hPre) (hPreBand := hPreBand) (hPostBand := hPostBand) (hPayNonneg := hPayNonneg) (hPaySummable := hPaySummable)
  exact
    avram_p4_d_dividend_original_countable_rightjump_local_secant_summable
      X x D w q hjump t ω hPre (max 1 (K : ℝ))
      (le_max_left 1 (K : ℝ)) hPayNonneg hPaySummable hLocal
