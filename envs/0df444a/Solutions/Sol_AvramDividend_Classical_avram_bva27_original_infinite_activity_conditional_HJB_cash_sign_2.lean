-- Prove2me | solution 2 for AvramDividend.Classical.avram_bva27_original_infinite_activity_conditional_HJB_cash_sign
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T09:01:23.911528+00:00
-- url     : https://prove2.me/submissions/6944c6be-1b8d-41fd-8a47-4fd9c0f3e304
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_preterminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_a07_condexp_upper_of_two_centered_noises
import Theorems.Thm_AvramDividend_Classical_avram_b20_BV_infinite_original_cash_one_conditional_martingale_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
    (T : ℝ) (hT : 0 < T)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ n : ℕ, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P (F n) ω ≤ w x := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  change ∀ n, ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P (F n) ω ≤ w x
  have hcut (n : ℕ) : 0 ≤ T - δ n := by
    dsimp [δ]
    have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hn).2
    nlinarith [mul_nonneg (le_of_lt hT)
      (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)]
  have hCashI (n : ℕ) :
      Integrable (fun ω : Ω =>
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P :=
    avram_p3_bv_original_strict_cash_L1
      X x C D hD q (le_of_lt hq) (T - δ n) (hcut n)
  have hTermI :
      Integrable (fun ω : Ω =>
        if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0) P :=
    avram_p3_bv_original_strict_preterminal_L1
      X hBV X.X_zero inferInstance x D hD.1.1 w hw_cont hw_neg q S
  have hSource := avram_b20_BV_infinite_original_cash_one_conditional_martingale_source
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
    x hx hxc D hD hw_nonneg hjump T hT hInfinite
  intro n
  obtain ⟨M, hMI, hM0, hUpper⟩ := hSource n
  have hZero : P[(fun _ : Ω => (0 : ℝ)) | 𝓕.rightCont 0] =ᵐ[P]
      (fun _ : Ω => (0 : ℝ)) := by simp
  have hUpper' : ∀ᵐ ω ∂P, F n ω ≤ w x + M ω + (0 : ℝ) := by
    simpa using hUpper
  exact avram_a07_condexp_upper_of_two_centered_noises (𝓕 := 𝓕)
    (w x) (F n) M (fun _ => 0) ((hCashI n).add hTermI)
    hMI (integrable_zero Ω ℝ P) hM0 hZero hUpper'
