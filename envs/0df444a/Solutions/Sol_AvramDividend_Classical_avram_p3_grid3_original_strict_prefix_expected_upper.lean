-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_strict_prefix_expected_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T01:09:34.761515+00:00
-- url     : https://prove2.me/submissions/337e6177-b92d-489f-a902-f9ecab9f077a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_redux3_bv_original_cofinal_strict_mesh_expected_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_strict_discounted_cash_real_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Conditional reduction of the exact original prefix budget to an
independently owned cofinal strict mesh budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
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
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδle : ∀ n, δ n ≤ T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)
    ∀ n, (∫ ω, F n ω ∂P) ≤ w x := by
  intro S F n
  obtain ⟨u, huMono, huZero, huT, huCofinal, huBudget⟩ :=
    avram_redux3_bv_original_cofinal_strict_mesh_expected_budget
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos
  have hs : 0 ≤ T - δ n := sub_nonneg.mpr (hδle n)
  have hsLT : T - δ n < T := sub_lt_self T (hδpos n)
  obtain ⟨k, hsk⟩ := huCofinal (T - δ n) hsLT
  let cash : ℝ → Ω → ℝ := fun a ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio a,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let term : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0
  have hStrat : IsDividendStrategy 𝓕 D := hD.1.1
  have hCashFull : Integrable (cash T) P := by
    exact avram_p3_bv_original_strict_cash_L1
      X x C D hD q (le_of_lt hq) T hT
  have hFull : Integrable (fun ω => cash T ω + term ω) P := by
    exact avram_p3_bv_original_prebudget_L1
      X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq) T hT
  have hTerm : Integrable term P := by
    have hDiff := hFull.sub hCashFull
    have heq : ((fun ω : Ω => cash T ω + term ω) - cash T) = term := by
      funext ω
      simp only [Pi.sub_apply]
      ring
    simpa only [heq] using hDiff
  have hCashS : Integrable (cash (T - δ n)) P := by
    exact avram_p3_bv_original_strict_cash_L1
      X x C D hD q (le_of_lt hq) (T - δ n) hs
  have hCashU : Integrable (cash (u k)) P := by
    exact avram_p3_bv_original_strict_cash_L1
      X x C D hD q (le_of_lt hq) (u k) (huZero k)
  have hPoint : ∀ ω : Ω,
      cash (T - δ n) ω + term ω ≤ cash (u k) ω + term ω := by
    intro ω
    have hm := avram_p3_grid3_original_strict_discounted_cash_real_monotone
      X q (le_of_lt hq) x D hStrat ω
      (T - δ n) (u k) hs (le_of_lt hsk)
    change cash (T - δ n) ω ≤ cash (u k) ω at hm
    simpa only [add_comm] using (add_le_add_right hm (term ω))
  have hMean : (∫ ω, cash (T - δ n) ω + term ω ∂P) ≤
      (∫ ω, cash (u k) ω + term ω ∂P) :=
    integral_mono (hCashS.add hTerm) (hCashU.add hTerm) hPoint
  change (∫ ω, cash (T - δ n) ω + term ω ∂P) ≤ w x
  exact hMean.trans (huBudget k)
