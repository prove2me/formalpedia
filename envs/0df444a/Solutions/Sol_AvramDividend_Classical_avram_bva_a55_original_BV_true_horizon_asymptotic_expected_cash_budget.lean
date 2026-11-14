-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a55_original_BV_true_horizon_asymptotic_expected_cash_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:22:44.908202+00:00
-- url     : https://prove2.me/submissions/d0f0058f-5b0e-4174-9fb6-3b34da75dd16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a56_original_BV_true_ruinclipped_Ito_Stieltjes_expected_cash_witness
import Theorems.Thm_AvramDividend_Classical_avram_bva33_original_BV_infinite_activity_inner_cash_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_one_sided_hjb_expected_budget
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
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m in (atTop : Filter ℕ),
        (∫ ω, F m ω ∂P) ≤ w x + ε := by
  classical
  intro δ S F ε hε
  apply Filter.Eventually.of_forall
  intro m
  obtain ⟨τ, hτeq, hτBound, hτStop, hτRuin, W, Cash, Term,
    M, G, H, hW, hCash, hTerm, hTermI, hCashI, hMI, hGI,
    hHI, hMzero, hGH, hUpper, hFdom⟩ :=
    avram_bva_a56_original_BV_true_ruinclipped_Ito_Stieltjes_expected_cash_witness
      X hX hBV q hq w C hC hw_cont hw0 hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD
      hw_nonneg hjump T hT hInfinite m
  have hSmooth : (¬ X.BoundedVariation →
      ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) := by
    constructor
    · intro hn
      exact False.elim (hn hBV)
    · intro _
      exact hw_smooth
  have hReward :
      (∫ ω, Term ω + Cash ω ∂P) ≤ w x :=
    (avram_wave6_06_original_one_sided_hjb_expected_budget
      X q hq w C hC hw0 hw_cont hw_neg hSmooth
      hw_gen hw_grad x hx hxc D hD τ S hτBound hτStop
      hτRuin W Cash Term M G H hW hCash hTerm
      hTermI hCashI hMI hGI hHI hMzero hGH hUpper).2.1
  have hFI : Integrable (F m) P :=
    (avram_bva33_original_BV_infinite_activity_inner_cash_terminal_integrable
      X hX hBV q hq w C hC hw_cont hw0 hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD
      hw_nonneg hjump T hT hInfinite) m
  have hDominated :
      (∫ ω, F m ω ∂P) ≤ (∫ ω, Term ω + Cash ω ∂P) :=
    integral_mono_ae hFI (hTermI.add hCashI) hFdom
  linarith
