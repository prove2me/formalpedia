-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:53:08.579806+00:00
-- url     : https://prove2.me/submissions/ef0cd3b6-c839-46a6-b2f9-c9e985de459f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 < q) (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T,le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ n, Integrable (F n) P := by
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
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0
  have hCash : Integrable Cash P := by
    simpa only [Cash] using
      (avram_p3_bv_original_strict_cash_L1
        X x C D hD q (le_of_lt hq) (T - δ n) hTinner)
  have hCashFull : Integrable CashFull P := by
    simpa only [CashFull] using
      (avram_p3_bv_original_strict_cash_L1
        X x C D hD q (le_of_lt hq) T (le_of_lt hT))
  have hFull : Integrable (fun ω => CashFull ω + Term ω) P := by
    simpa only [CashFull, Term, S] using
      (avram_p3_bv_original_prebudget_L1
        X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq) T (le_of_lt hT))
  have hTerm : Integrable Term P := by
    have hSub := hFull.sub hCashFull
    have hEq : ((fun ω => CashFull ω + Term ω) - CashFull) = Term := by
      funext ω
      change CashFull ω + Term ω - CashFull ω = Term ω
      ring
    exact hEq ▸ hSub
  change Integrable (Cash + Term) P
  exact hCash.add hTerm
