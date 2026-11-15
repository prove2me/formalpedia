-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_finitecap_original_single_clock_strict_cash_plus_true_T_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:52:07.849409+00:00
-- url     : https://prove2.me/submissions/b1f3eac7-91da-4637-8a56-7d6a9e74c06b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_uniform_physical_nol1_cell_certificate
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_physical_B_full_pointwise_nonpositive_ae
import Theorems.Thm_AvramDividend_Classical_avram_a19_uniform_delta_profile
import Theorems.Thm_AvramDividend_Classical_avram_a19_discounted_cash_terminal_prefix_budget_mono
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_discounted_cash_finite_all_paths
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_strict_terminal_joint_L1_and_source_mean_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
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
    (T : ℝ) (hT : 0 < T) (hFinite : C ≠ ⊤)
    (s : ℝ) (hs0 : 0 ≤ s) (hsT : s < T) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio s,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0) ∂P) ≤ w x := by
  classical
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let v : ℕ → ℝ := fun n => T - δ n
  obtain ⟨hδPos, hδLe, hδAnti, hδTend⟩ :=
    avram_a19_uniform_delta_profile T hT
  have hvMono : Monotone v := by
    intro i j hij; dsimp [v]; exact sub_le_sub_left (hδAnti hij) T
  have hvNonneg (n : ℕ) : 0 ≤ v n := by dsimp [v]; linarith [hδLe n]
  have hvBelow (n : ℕ) : v n ≤ T := by dsimp [v]; linarith [hδPos n]
  have hvTend : Tendsto v atTop (𝓝 T) := by
    simpa only [v, sub_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => T) atTop (𝓝 T)).sub hδTend)
  have hvCover : ∀ r : ℝ, r < T → ∃ n, r < v n := by
    intro r hr; exact (hvTend.eventually (isOpen_Ioi.mem_nhds hr)).exists
  obtain ⟨u, M, B, Err, huGrid, huMono, huUniform, hBDef,
    hM, hErrInt, hErrMean, hPhysical⟩ :=
    avram_bv_strict6_original_uniform_physical_nol1_cell_certificate
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT
  have hBNeg (n : ℕ) : ∀ᵐ ω ∂P, B n ω ≤ 0 := by
    have hBound := avram_p3_grid4_original_physical_B_full_pointwise_nonpositive_ae
      X hBV q w C hw_gen hw_grad x D (u n) n (huMono n)
    filter_upwards [hBound] with ω hb
    simpa only [hBDef n ω] using hb
  have hP : ∀ n, ∀ᵐ ω ∂P,
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (v n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0) ≤
    w x + (M n ω + B n ω) + max (Err n ω) 0 := by
    intro n
    simpa only [v, δ, S] using hPhysical n
  have hFull := avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
    X hBV x C D hD w hw_cont hw_neg q hq.le S v hvMono
    hvNonneg hvBelow hvCover M B Err
    (fun n => ⟨(hM n).1, le_of_eq (hM n).2⟩)
    hBNeg hErrInt hErrMean hP
  let Term : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0
  have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
  have hFiniteCash : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≠ ⊤ := by
    filter_upwards [] with ω
    exact avram_limit2_original_strict_discounted_cash_finite_all_paths
      X q hq.le x D hDiv ω T (le_of_lt hT)
  have hCashS : Integrable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio s,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P :=
    avram_p3_bv_original_strict_cash_L1 X x C D hD q hq.le s hs0
  have hCashT : Integrable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P :=
    avram_p3_bv_original_strict_cash_L1 X x C D hD q hq.le T (le_of_lt hT)
  have hTermI : Integrable Term P := by
    have hh := avram_p3_g2_original_BV_strict_terminal_joint_L1_and_source_mean_le
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hx hxc D hD q hjump S
    exact hh.2.1
  have hPrefix := avram_a19_discounted_cash_terminal_prefix_budget_mono
    P D (ruinTime X x D) q s T (le_of_lt hsT) Term
    hFiniteCash hCashS hCashT hTermI
  have hST : (S : ℝ) = T := rfl
  have hFullBudget :
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      Term ω ∂P) ≤ w x := by
    simpa only [hST, Term] using hFull
  exact hPrefix.trans hFullBudget
