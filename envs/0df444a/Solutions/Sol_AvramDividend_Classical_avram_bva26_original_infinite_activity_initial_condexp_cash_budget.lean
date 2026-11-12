-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva26_original_infinite_activity_initial_condexp_cash_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:15:51.426946+00:00
-- url     : https://prove2.me/submissions/2da70f26-6c5a-4101-ada2-2509dfa91b7f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_bva27_original_infinite_activity_conditional_HJB_cash_sign
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_reward_L1_nonnegative
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
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
    ∀ n : ℕ, Integrable (F n) P ∧
      (∀ᵐ ω ∂P,
        condExp (𝓕.rightCont 0) P (F n) ω ≤ w x) := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro δ S F n
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 2 := by
    have hnat : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by linarith
  have hTinner : 0 ≤ T - δ n := by
    have hMul : T ≤ T * ((n : ℝ) + 2) := by
      nlinarith [mul_nonneg (le_of_lt hT) (sub_nonneg.mpr hn1)]
    have hDiv : T / ((n : ℝ) + 2) ≤ T :=
      (div_le_iff₀ hn2).2 hMul
    dsimp [δ]
    linarith
  let Cash : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let CashFull : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let Term : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω)
    else 0
  have hCash : Integrable Cash P := by
    simpa only [Cash] using
      (avram_p3_bv_original_strict_cash_L1
        X x C D hD q (le_of_lt hq) (T - δ n) hTinner)
  have hCashFull : Integrable CashFull P := by
    simpa only [CashFull] using
      (avram_p3_bv_original_strict_cash_L1
        X x C D hD q (le_of_lt hq) T (le_of_lt hT))
  have hFull : Integrable (fun ω => CashFull ω + Term ω) P := by
    have hReward :=
      avram_p3_bv_original_strict_reward_L1_nonnegative
        X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq)
        T (le_of_lt hT) hT hw_nonneg
    simpa only [CashFull, Term, S] using hReward.1
  have hTerm : Integrable Term P := by
    have hSub := hFull.sub hCashFull
    have hEq : ((fun ω => CashFull ω + Term ω) - CashFull) = Term := by
      funext ω
      change CashFull ω + Term ω - CashFull ω = Term ω
      ring
    exact hEq ▸ hSub
  have hF : Integrable (F n) P := by
    change Integrable (Cash + Term) P
    exact hCash.add hTerm
  have hBudget :=
    avram_bva27_original_infinite_activity_conditional_HJB_cash_sign
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump T hT hInfinite
  exact ⟨hF, hBudget n⟩
