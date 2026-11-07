-- Prove2me | solution 1 for AvramDividend.Classical.avram_route10_original_BV_positive_error_fatou_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T14:40:42.934046+00:00
-- url     : https://prove2.me/submissions/3cea3fc4-318b-4c99-a5ba-ed9fcb94f1b7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_strict_prefix_margin_sequence
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_survival_preterminal_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_source_vanishing_mean_physical_cells
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
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
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let Y : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)
    (0 ≤ᵐ[P] Y) ∧
    ∃ F M B E : ℕ → Ω → ℝ,
      (∀ n, Measurable (F n)) ∧
      (∀ n, Integrable (F n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F n) ∧
      (∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) = 0) ∧
      (∀ n, Integrable (fun ω => max (E n ω) 0) P) ∧
      Tendsto (fun n => ∫ ω, max (E n ω) 0 ∂P) atTop (nhds (0 : ℝ)) ∧
      (∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F n ω ≤ w x + M n ω + B n ω + max (E n ω) 0) ∧
      (∀ᵐ ω ∂P,
        ENNReal.ofReal (Y ω) ≤
          liminf (fun n => ENNReal.ofReal (F n ω)) atTop) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  obtain ⟨hδpos, hδle, hδanti, hδlimit⟩ :=
    AvramDividend.Classical.avram_p3_grid3_strict_prefix_margin_sequence T hTpos
  let S : ℝ≥0 := ⟨T, hT⟩
  let Y : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω)
    else 0)
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω)
    else 0)
  have hYPos : 0 ≤ᵐ[P] Y := by
    filter_upwards [] with ω
    have ht := AvramDividend.Classical.avram_limit2_original_strict_survival_preterminal_nonnegative
      X q x w D T hT hTpos hw_nonneg ω
    exact add_nonneg ENNReal.toReal_nonneg ht
  obtain ⟨hF, hFatou⟩ :=
    AvramDividend.Classical.avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
      X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq)
      T hTpos hw_nonneg δ hδpos hδle hδanti hδlimit
  obtain ⟨M0, B0, E, hBudget, hE, hEMean, hPhysical⟩ :=
    AvramDividend.Classical.avram_p3_grid4_original_source_vanishing_mean_physical_cells
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hTpos
  have hCentre (n : ℕ) :
      ∃ m b : Ω → ℝ,
        Integrable m P ∧ (∫ ω, m ω ∂P) = 0 ∧
        (∀ ω, b ω ≤ 0) ∧
        (∀ ω, M0 n ω + B0 n ω = m ω + b ω) := by
    let Z : Ω → ℝ := fun ω => M0 n ω + B0 n ω
    let b : ℝ := ∫ ω, Z ω ∂P
    refine ⟨(fun ω => Z ω - b), (fun _ => b), ?_, ?_, ?_, ?_⟩
    · exact (hBudget n).1.sub (integrable_const b)
    · rw [integral_sub (hBudget n).1 (integrable_const b)]
      simp [b, Z]
    · intro ω
      simpa [b, Z] using (hBudget n).2
    · intro ω
      dsimp [Z]
      ring
  choose M B hMInt hMMean hBNeg hEqual using hCentre
  have hPhysical' : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w x + M n ω + B n ω + max (E n ω) 0 := by
    intro n
    filter_upwards [hPhysical n] with ω hp
    have hEq : M0 n ω + B0 n ω = M n ω + B n ω := hEqual n ω
    have hp' : F n ω ≤ w x + (M n ω + B n ω) + max (E n ω) 0 := by
      simpa only [F, S, hEq] using hp
    linarith
  have hFatou' : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Y ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop := by
    filter_upwards [] with ω
    simpa only [Y, F, S] using hFatou ω
  refine ⟨hYPos, F, M, B, E, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun n => (hF n).1
  · exact fun n => (hF n).2.1
  · intro n
    exact Filter.Eventually.of_forall (hF n).2.2
  · exact fun n => ⟨hMInt n, hMMean n⟩
  · exact hE
  · exact hEMean
  · intro n
    exact Filter.Eventually.of_forall (hBNeg n)
  · exact hPhysical'
  · exact hFatou'
