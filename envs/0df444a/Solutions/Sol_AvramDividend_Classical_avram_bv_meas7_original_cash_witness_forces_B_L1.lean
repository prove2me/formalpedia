-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_meas7_original_cash_witness_forces_B_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:44:48.310543+00:00
-- url     : https://prove2.me/submissions/c16c4460-046a-4c1e-bd17-bba70483b36d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_arbitrary_grid_B_aestronglyMeasurable_auto
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_physical_B_full_pointwise_nonpositive_ae
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn8b_original_B_L1_from_true_strict_cash_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The literal original BV stopped HJB source is integrable once its true
same-grid cash inequality and positive error estimate have been established. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (M Err : ℕ → Ω → ℝ) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let B : ℕ → Ω → ℝ := fun n ω =>
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      (∑ i ∈ Finset.range (n + 1),
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) *
            (X.generator w (Z i) - q * w (Z i)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0) +
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
       let R : ℝ≥0 → ℝ := fun t =>
         ((t : ℝ) * X.drift - X.X t ω) - J t
       ∑ i ∈ Finset.range (n + 1),
         (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
             0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
          else 0) * (R (u n i) - R (u n (i + 1))))
    let Pay : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)
    (∀ n, Integrable (M n) P) →
    (∀ n, Integrable (fun ω => max (Err n ω) 0) P) →
    (∀ n, ∀ᵐ ω ∂P,
      Pay n ω ≤ w x + (M n ω + B n ω) + max (Err n ω) 0) →
    ∀ n, Integrable (B n) P := by
  intro δ S B Pay hMint hErr hPath
  have hBMeas : ∀ n, AEStronglyMeasurable (B n) P := by
    intro n
    simpa only [B] using
      (avram_bv_meas7_original_arbitrary_grid_B_aestronglyMeasurable_auto
        X hX hBV q w hw_cont hw_neg C x D hD u n)
  have hBNeg : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0 := by
    intro n
    have hbase :=
      avram_p3_grid4_original_physical_B_full_pointwise_nonpositive_ae
        X hBV q w C hw_gen hw_grad x D (u n) n (hmono n)
    filter_upwards [hbase] with ω hω
    simpa only [B] using hω
  have hPayPos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Pay n ω := by
    intro n
    filter_upwards [] with ω
    have hCash : 0 ≤
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal :=
      ENNReal.toReal_nonneg
    have hTerm : 0 ≤
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
         else 0) := by
      split_ifs with hSurv
      · have hSpos : (0 : ℝ≥0) < S := by
          exact_mod_cast hT
        exact mul_nonneg (Real.exp_pos _).le
          (hw_nonneg ω S hSpos hSurv)
      · exact le_refl _
    exact add_nonneg hCash hTerm
  exact avram_p3_grid4_turn8b_original_B_L1_from_true_strict_cash_budget
    X q w x D T (le_of_lt hT) S rfl δ Pay M B Err
    (by intro n ω; rfl) hMint hErr hBMeas hBNeg hPayPos hPath
