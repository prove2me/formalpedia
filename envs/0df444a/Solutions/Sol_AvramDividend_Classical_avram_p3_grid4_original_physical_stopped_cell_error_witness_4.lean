-- Prove2me | solution 4 for AvramDividend.Classical.avram_p3_grid4_original_physical_stopped_cell_error_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:28:42.40387+00:00
-- url     : https://prove2.me/submissions/c21dc77a-ab55-4067-b022-c842a0a0bae8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_uniform_physical_nol1_cell_certificate
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn8b_original_B_L1_from_true_strict_cash_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn8b_original_uniform_full_B_aestronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_physical_B_full_pointwise_nonpositive_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Exact original grid, with L1 drift source derived from its cash budget. -/
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
    ∃ (u : ℕ → ℕ → ℝ≥0) (M B Err : ℕ → Ω → ℝ),
      (∀ n, u n 0 = 0 ∧ ((u n (n + 1) : ℝ) = T - δ n)) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n ω,
        let Z : ℕ → ℝ := fun i => Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
        B n ω =
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
             else 0) * (R (u n i) - R (u n (i + 1))))) ∧
      (∀ n, Integrable (M n) P ∧
        (∫ ω, M n ω ∂P) = 0 ∧ Integrable (B n) P) ∧
      (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
      Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (𝓝 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0) ≤
        w x + (M n ω + B n ω) + max (Err n ω) 0) := by
  obtain ⟨u, M, B, Err, hGrid, hMono, hUniform, hB,
      hMInt, hErrInt, hErrLim, hBudget⟩ :=
    avram_bv_strict6_original_uniform_physical_nol1_cell_certificate
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  let Pay : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) *
        w (riskProcess X x D S ω)
     else 0)
  have hPayExact : ∀ n ω, Pay n ω =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (riskProcess X x D S ω)
       else 0) := by intros; rfl
  have hBMeas : ∀ n, AEStronglyMeasurable (B n) P := by
    intro n
    have hm :=
      avram_p3_grid4_turn8b_original_uniform_full_B_aestronglyMeasurable
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT
        u hGrid hMono hUniform n
    convert hm using 1
    funext ω
    exact hB n ω
  have hBNeg : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0 := by
    intro n
    have hs := avram_p3_grid4_original_physical_B_full_pointwise_nonpositive_ae
      X hBV q w C hw_gen hw_grad x D (u n) n (hMono n)
    filter_upwards [hs] with ω hsω
    rw [hB n ω]
    exact hsω
  have hPayPos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Pay n ω := by
    intro n
    filter_upwards [] with ω
    have hCash : 0 ≤
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal :=
      ENNReal.toReal_nonneg
    have hTerm : 0 ≤
        (if (S : ℝ≥0∞) <
            ruinTime X x D ω then
          Real.exp (-(q * T)) *
            w (riskProcess X x D S ω)
         else 0) := by
      split_ifs with hSurv
      · have hSpos : (0 : ℝ≥0) < S := by
          exact_mod_cast hT
        exact mul_nonneg (Real.exp_pos _).le
          (hw_nonneg ω S hSpos hSurv)
      · exact le_refl _
    exact add_nonneg hCash hTerm
  have hPayPath : ∀ n, ∀ᵐ ω ∂P,
      Pay n ω ≤ w x + (M n ω + B n ω) + max (Err n ω) 0 := by
    intro n
    simpa only [Pay, δ] using hBudget n
  have hBInt : ∀ n, Integrable (B n) P := by
    exact avram_p3_grid4_turn8b_original_B_L1_from_true_strict_cash_budget
      X q w x D T (le_of_lt hT) S rfl δ Pay M B Err hPayExact
      (fun n => (hMInt n).1) hErrInt hBMeas hBNeg hPayPos hPayPath
  refine ⟨u, M, B, Err, hGrid, hMono, hB, ?_, hErrInt, hErrLim, hBudget⟩
  intro n
  exact ⟨(hMInt n).1, (hMInt n).2, hBInt n⟩
