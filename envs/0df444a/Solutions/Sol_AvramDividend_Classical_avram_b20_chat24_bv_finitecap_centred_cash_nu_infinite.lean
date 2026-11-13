-- Prove2me | solution 1 for AvramDividend.Classical.avram_b20_chat24_bv_finitecap_centred_cash_nu_infinite
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:15:03.8331+00:00
-- url     : https://prove2.me/submissions/a24dc083-9234-4114-b807-4146b46450b9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_preterminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_bvb_original_BV_infinite_activity_expected_inner_reward_le
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
    (hFinite : C ≠ ⊤)
    (hnu : X.ν (Iio (0 : ℝ)) = ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)
    ∃ (M Err : ℕ → Ω → ℝ) (η : ℕ → ℝ),
      (∀ n, 0 < η n) ∧
      Tendsto η atTop (nhds (0 : ℝ)) ∧
      (∀ n, Integrable (M n) P ∧
        (∫ ω, M n ω ∂P) = 0) ∧
      (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F n ω ≤ w x + M n ω + max (Err n ω) 0) ∧
      (∀ n, (∫ ω, max (Err n ω) 0 ∂P) ≤ η n) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  change ∃ (M Err : ℕ → Ω → ℝ) (η : ℕ → ℝ), (∀ n, 0 < η n) ∧ Tendsto η atTop (nhds 0) ∧
    (∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) = 0) ∧
    (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
    (∀ n, ∀ᵐ ω ∂P, F n ω ≤ w x + M n ω + max (Err n ω) 0) ∧
    (∀ n, (∫ ω, max (Err n ω) 0 ∂P) ≤ η n)
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
  have hFI (n : ℕ) : Integrable (F n) P := by
    exact (hCashI n).add hTermI
  have hInt : ¬ X.ν (Iio (0 : ℝ)) < ⊤ := by simp [hnu]
  have hExpected (n : ℕ) : (∫ ω, F n ω ∂P) ≤ w x := by
    have hAll := avram_bvb_original_BV_infinite_activity_expected_inner_reward_le
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hInt
    exact hAll n
  refine ⟨(fun n ω => F n ω - ∫ z, F n z ∂P),
    (fun _ _ => 0), (fun n => (1 / 2 : ℝ) ^ n), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n; positivity
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  · intro n
    constructor
    · exact (hFI n).sub (integrable_const _)
    · rw [integral_sub (hFI n) (integrable_const _)]
      simp
  · intro n
    simpa using (integrable_zero Ω ℝ P)
  · intro n
    filter_upwards [] with ω
    simp only [max_self, add_zero]
    linarith [hExpected n]
  · intro n; simp
