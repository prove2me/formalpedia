-- Prove2me | solution 4 for AvramDividend.Classical.avram_bva26_original_infinite_activity_initial_condexp_cash_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:36:44.080943+00:00
-- url     : https://prove2.me/submissions/0d6a983a-6064-4bf6-9ae7-838f3648cc11
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b20_BV_infinite_original_cash_one_conditional_martingale_source
import Theorems.Thm_AvramDividend_Classical_avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
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
  obtain ⟨M, hMI, hCE, hPath⟩ :=
    avram_b20_BV_infinite_original_cash_one_conditional_martingale_source
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump T hT hInfinite n
  have hFI : Integrable (F n) P :=
    (avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
      X hBV x C D hD w hw_cont hw_neg q hq T hT) n
  have hUpper : ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P (F n) ω ≤
      condExp (𝓕.rightCont 0) P (fun ω => w x + M ω) ω :=
    condExp_mono (m := 𝓕.rightCont 0)
      hFI ((integrable_const (w x)).add hMI) hPath
  have hAdd : ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P (fun ω => w x + M ω) ω =
      condExp (𝓕.rightCont 0) P (fun _ => w x) ω +
      condExp (𝓕.rightCont 0) P M ω :=
    condExp_add (integrable_const (w x)) hMI (𝓕.rightCont 0)
  refine ⟨hFI, ?_⟩
  filter_upwards [hUpper, hAdd, hCE] with ω hu ha hc
  calc
    condExp (𝓕.rightCont 0) P (F n) ω ≤
        condExp (𝓕.rightCont 0) P (fun ω => w x + M ω) ω := hu
    _ = w x + condExp (𝓕.rightCont 0) P M ω := by
      simpa only [condExp_const (𝓕.rightCont.le 0) (w x), Pi.add_apply] using ha
    _ = w x := by rw [hc, add_zero]
