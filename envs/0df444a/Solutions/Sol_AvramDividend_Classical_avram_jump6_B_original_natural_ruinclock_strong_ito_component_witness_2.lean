-- Prove2me | solution 2 for AvramDividend.Classical.avram_jump6_B_original_natural_ruinclock_strong_ito_component_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T15:36:22.011386+00:00
-- url     : https://prove2.me/submissions/eda6be66-e222-4888-a07a-7b81c7f3f272
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_original_right_payment_secant_from_gradient
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_positive_clock_stopped_signed_Ito_source_only
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxpos : 0 < x)
    (k : ℕ) (hk : 0 < k)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (k : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hCashI : Integrable Cash P) :
    ∃ M G H : Ω → ℝ,
          Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
          (∫ ω, M ω ∂P) = 0 ∧
          (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
          (∀ᵐ ω ∂P, Term ω + Cash ω ≤
            w x + M ω + G ω + H ω) := by
  have hGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y := by
    intro y hy hc
    have hMax := (hw_hjb y hy hc).2
    have hBound : 1 - deriv w y ≤
        max (X.generator w y - q * w y) (1 - deriv w y) :=
      le_max_right _ _
    rw [hMax] at hBound
    linarith
  have hjump :=
    avram_sweep16_20261106_original_right_payment_secant_from_gradient
      X x C hC hxc D hD w hw_cont hw_smooth hGrad
  obtain ⟨M, G, H, hMI, hGI, hHI, hMmean,
      hMzero, hGzero, hHzero, hGH, hPositive⟩ :=
    avram_jump6_B_original_positive_clock_stopped_signed_Ito_source_only
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_hjb
      x hx hxc D hD hxpos k hk τ hτeq hτmeas hτstop
      W Cash Term hW hCash hTerm hCashI
  refine ⟨M, G, H, hMI, hGI, hHI, hMmean, hGH, ?_⟩
  filter_upwards [hMzero, hGzero, hHzero, hPositive]
    with ω hM0 hG0 hH0 hPos
  by_cases hZero : τ ω = 0
  · have hBound :=
      avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
        X x q w C D hD hjump τ W Cash Term
        hW hCash hTerm ω hZero
    simpa [hM0 hZero, hG0 hZero, hH0 hZero] using hBound
  · exact hPos hZero
