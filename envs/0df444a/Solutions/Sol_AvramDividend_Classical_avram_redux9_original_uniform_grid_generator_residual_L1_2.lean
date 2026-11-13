-- Prove2me | solution 2 for AvramDividend.Classical.avram_redux9_original_uniform_grid_generator_residual_L1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:43:30.715186+00:00
-- url     : https://prove2.me/submissions/c39b3e60-def0-4fdb-8550-b721e9b559ea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_uniform_original_physical_nonintegrable_error_witness
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn8b_original_B_L1_from_true_strict_cash_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn8b_original_uniform_full_B_aestronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_physical_B_full_pointwise_nonpositive_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV :
    X.BoundedVariation) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧
    X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0
    → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t :
    ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t
    ω))) (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0) (hgrid : ∀ n, u n 0 = 0 ∧ ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2))) (hmono : ∀ n i, i < n + 1 → u n i ≤ u n
    (i + 1)) (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2);
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩;
    ∃ B : ℕ → Ω → ℝ, (∀ n ω, let Z : ℕ → ℝ := fun i => Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i); B n ω = (∑ i ∈ Finset.range (n +
    1), if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z i ∧ ENNReal.ofReal (Z i) < C then Real.exp (-(q * (u n i : ℝ))) * (X.generator w (Z i) - q * w (Z i)) * ((u
    n (i + 1) : ℝ) - (u n i : ℝ)) else 0) + (let J : ℝ≥0 → ℝ := fun t => ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
    else 0; let R : ℝ≥0 → ℝ := fun t => ((t : ℝ) * X.drift - X.X t ω) - J t; ∑ i ∈ Finset.range (n + 1), (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z i ∧
    ENNReal.ofReal (Z i) < C then Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i) else 0) * (R (u n i) - R (u n (i + 1))))) ∧ (∀ n, Integrable (B n) P) := by
  classical
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
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
            else 0
           let R : ℝ≥0 → ℝ := fun t =>
            ((t : ℝ) * X.drift - X.X t ω) - J t
           ∑ i ∈ Finset.range (n + 1),
             (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
                 0 < Z i ∧ ENNReal.ofReal (Z i) < C then
               Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
             else 0) * (R (u n i) - R (u n (i + 1))))
  refine ⟨B, ?_, ?_⟩
  · intro n ω
    rfl
  · let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let Pay : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
       else 0)
    obtain ⟨M, Err, hM, hMeasExcess, hErrI, hErrLim, hBudget⟩ :=
      avram_a19_uniform_original_physical_nonintegrable_error_witness
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT
        u hgrid hmono huniform B (by intro n ω; rfl)
    have hMeas : ∀ n, AEStronglyMeasurable (B n) P := by
      intro n
      simpa only [B] using
        (avram_p3_grid4_turn8b_original_uniform_full_B_aestronglyMeasurable
          X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
          hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT
          u hgrid hmono huniform n)
    have hNeg : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0 := by
      intro n
      simpa only [B] using
        (avram_p3_grid4_original_physical_B_full_pointwise_nonpositive_ae
          X hBV q w C hw_gen hw_grad x D (u n) n (hmono n))
    have hPayPos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Pay n ω := by
      intro n
      filter_upwards [] with ω
      have hCash : 0 ≤
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal := ENNReal.toReal_nonneg
      have hTerm : 0 ≤
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
           else 0) := by
        split_ifs with hSurv
        · have hSpos : (0 : ℝ≥0) < S := by exact_mod_cast hT
          exact mul_nonneg (Real.exp_pos _).le
            (hw_nonneg ω S hSpos hSurv)
        · exact le_refl _
      exact add_nonneg hCash hTerm
    have hPayPath : ∀ n, ∀ᵐ ω ∂P,
        Pay n ω ≤ w x + (M n ω + B n ω) + max (Err n ω) 0 := by
      intro n
      simpa only [Pay, δ] using hBudget n
    exact avram_p3_grid4_turn8b_original_B_L1_from_true_strict_cash_budget
      X q w x D T (le_of_lt hT) S rfl δ Pay M B Err (by intros; rfl)
      (fun n => (hM n).1) hErrI hMeas hNeg hPayPos hPayPath
