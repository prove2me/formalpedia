-- Prove2me | solution 10 for AvramDividend.Classical.avram_p3_grid4_original_source_vanishing_mean_physical_cells
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T07:27:16.097726+00:00
-- url     : https://prove2.me/submissions/c2cbe397-0001-4b74-8e07-8dc646cae466
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva42_uniform_physical_grid_canonical
import Theorems.Thm_AvramDividend_Classical_avram_bvb_original_uniform_grid_exists_exact_B_nonpositive_and_true_prepayment
import Theorems.Thm_AvramDividend_Classical_avram_a19_nonint_original_compensated_error_without_meas
import Theorems.Thm_AvramDividend_Classical_avram_a19_nonint_original_B_uniform_aestronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_bva44_probability_signed_B_integrable_of_one_sided_error
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    ∃ M B Err : ℕ → Ω → ℝ,
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
      Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (𝓝 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0) ≤
        w x + (M n ω + B n ω) + max (Err n ω) 0) := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨u, hgrid, hu, huniform⟩ :=
    avram_bva42_uniform_physical_grid_canonical T hT
  have hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1) := by
    intro n i _
    exact hu n i
  obtain ⟨B, hB, hBsign, _⟩ :=
    avram_bvb_original_uniform_grid_exists_exact_B_nonpositive_and_true_prepayment
      X hX hBV q w C hw_gen x D hD.1.1 T hT u hu huniform
  obtain ⟨M, Err, hMI, hEI, hErr, hBudget⟩ :=
    avram_a19_nonint_original_compensated_error_without_meas
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      T hT u hgrid hmono huniform B hB
  have hBmeas : ∀ n, AEStronglyMeasurable (B n) P :=
    avram_a19_nonint_original_B_uniform_aestronglyMeasurable
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      T hT u hgrid hmono huniform B hB
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  have hFI : ∀ n, Integrable (F n) P := by
    intro n
    simpa only [F, δ, S] using
      (avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
        X hBV x C D hD w hw_cont hw_neg q hq T hT n)
  have hBn : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0 := by
    intro n
    filter_upwards [hBsign] with ω hω
    exact hω n
  have hBI : ∀ n, Integrable (B n) P := by
    intro n
    have hOriginal : ∀ᵐ ω ∂P,
        F n ω ≤ w x + (M n ω + B n ω) + max (Err n ω) 0 := by
      simpa only [F, δ, S] using (hBudget n)
    have hReassoc : ∀ᵐ ω ∂P,
        F n ω ≤ w x + M n ω + B n ω + max (Err n ω) 0 := by
      filter_upwards [hOriginal] with ω hw
      calc
        F n ω ≤ w x + (M n ω + B n ω) + max (Err n ω) 0 := hw
        _ = w x + M n ω + B n ω + max (Err n ω) 0 := by ring
    exact avram_bva44_probability_signed_B_integrable_of_one_sided_error
      P (F n) (M n) (B n) (Err n) (w x)
      (hFI n) (hMI n).1 (hEI n) (hBmeas n) (hBn n) hReassoc
  have hSource : ∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
      (∫ ω, M n ω + B n ω ∂P) ≤ 0 := by
    intro n
    constructor
    · exact (hMI n).1.add (hBI n)
    · calc
        (∫ ω, M n ω + B n ω ∂P) =
            (∫ ω, M n ω ∂P) + (∫ ω, B n ω ∂P) :=
          integral_add (hMI n).1 (hBI n)
        _ = (∫ ω, B n ω ∂P) := by rw [(hMI n).2]; simp
        _ ≤ 0 := integral_nonpos_of_ae (hBn n)
  exact ⟨M, B, Err, hSource, hEI, hErr, hBudget⟩
