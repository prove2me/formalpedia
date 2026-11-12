-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger112_original_strict_interior_cell_cash_rate_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T15:58:23.190204+00:00
-- url     : https://prove2.me/submissions/008d0208-5dd5-4810-82b9-d2d805b14f3c

import Theorems.Thm_AvramDividend_Classical_avram_gledger99_original_interior_contact_cells_sum_bound
import Theorems.Thm_AvramDividend_Classical_avram_gledger94_original_dividend_cell_measure_finite
import Theorems.Thm_AvramDividend_Classical_avram_gledger109_monotone_finite_cell_real_mass_partition
import Theorems.Thm_AvramDividend_Classical_avram_gledger106_original_ruinclipped_strict_mass_le_cash
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original interior contact and strict cash are charged once per cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (n ρ δ : ℝ≥0) (hρn : ρ ≤ n) (hρruin : (ρ : ℝ≥0∞) ≤ ruinTime X x D ω)
    (u : ℝ) (hu : 0 ≤ u)
    (hprefix : ∀ t : ℝ≥0, 0 < t → t < ρ → u ≤ riskProcess X x D t ω)
    (v : ℕ → ℝ≥0) (hv : Monotone v) (hv0 : v 0 = 0)
    (k : ℕ) (hvk : v k < ρ) (hinterior : ∀ i : ℕ, i < k → v (i + 1) < ρ)
    (hwidth : ∀ i : ℕ, i < k → (v (i + 1) : ℝ) - (v i : ℝ) ≤ (δ : ℝ))
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hTopCap : C = ⊤) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    (Finset.sum (Finset.range k) (fun i => (∫⁻ s in Ioc (v i : ℝ) (v (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (v (i + 1) : ℝ))) *
        (w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
         w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω)))) ≤
    q * (δ : ℝ) * Real.exp (q * (n : ℝ)) *
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by
  have hcell : ∀ i : ℕ, i < k →
      dividendMeasure D ω (Ioc (v i : ℝ) (v (i + 1) : ℝ)) ≠ ⊤ := by
    intro i _
    exact avram_gledger94_original_dividend_cell_measure_finite D ω _ _
  have hcontact := avram_gledger99_original_interior_contact_cells_sum_bound
      X x D hD ω ρ u hu hprefix v hv k hinterior hcell
      q hq w C hTopCap hw0 hw_cont hw_neg hw_grad
  have hvr : Monotone (fun i : ℕ => (v i : ℝ)) := by
    intro i j hij; exact_mod_cast hv hij
  have hmassEq :
      (∑ i ∈ Finset.range k,
        (dividendMeasure D ω (Ioc (v i : ℝ) (v (i + 1) : ℝ))).toReal) =
      (dividendMeasure D ω (Ioc (0 : ℝ) (v k : ℝ))).toReal := by
    have hfin : dividendMeasure D ω (Ioc (v 0 : ℝ) (v k : ℝ)) < ⊤ :=
      lt_top_iff_ne_top.mpr
        (avram_gledger94_original_dividend_cell_measure_finite D ω _ _)
    simpa only [hv0, NNReal.coe_zero] using
      (avram_gledger109_monotone_finite_cell_real_mass_partition
        (dividendMeasure D ω) (fun i => (v i : ℝ)) hvr k hfin)
  have hsubset : Ioc (0 : ℝ) (v k : ℝ) ⊆ Ioo (0 : ℝ) (ρ : ℝ) := by
    intro t ht; exact ⟨ht.1, lt_of_le_of_lt ht.2 (by exact_mod_cast hvk)⟩
  have hupperfinite :
      dividendMeasure D ω (Ioo (0 : ℝ) (ρ : ℝ)) ≠ ⊤ := by
    have hs : Ioo (0 : ℝ) (ρ : ℝ) ⊆ Ioc (0 : ℝ) (ρ : ℝ) := by
      intro t ht; exact ⟨ht.1, le_of_lt ht.2⟩
    exact ne_of_lt (lt_of_le_of_lt (measure_mono hs)
      (lt_top_iff_ne_top.mpr
        (avram_gledger94_original_dividend_cell_measure_finite D ω _ _)))
  have hmassBound :
      (dividendMeasure D ω (Ioc (0 : ℝ) (v k : ℝ))).toReal ≤
      Real.exp (q * (n : ℝ)) *
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal := by
    apply le_trans (ENNReal.toReal_mono hupperfinite (measure_mono hsubset))
    exact avram_gledger106_original_ruinclipped_strict_mass_le_cash
      X x D hD ω q hq n ρ hρn hρruin
  calc
    _ ≤ _ := hcontact
    _ ≤ _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hw := mul_le_mul_of_nonneg_left (hwidth i (Finset.mem_range.mp hi)) hq
      exact mul_le_mul_of_nonneg_right hw ENNReal.toReal_nonneg
    _ = _ := congrArg (fun t : ℝ => q * (δ : ℝ) * t) hmassEq
    _ ≤ _ := mul_le_mul_of_nonneg_left hmassBound (mul_nonneg hq (by positivity))
    _ = _ := by ring
