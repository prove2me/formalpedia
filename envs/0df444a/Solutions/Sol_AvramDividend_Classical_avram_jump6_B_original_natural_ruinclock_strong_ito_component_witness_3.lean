-- Prove2me | solution 3 for AvramDividend.Classical.avram_jump6_B_original_natural_ruinclock_strong_ito_component_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:03:39.767654+00:00
-- url     : https://prove2.me/submissions/e19d15c9-37fb-436d-a0d1-d98e5ce988f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_original_right_payment_secant_from_gradient
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_positive_clock_stopped_signed_Ito_source_only
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
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
  have hgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y := by
    intro y hy hyC
    have hh : 1 - deriv w y ≤ 0 :=
      (le_max_right _ _).trans_eq (hw_hjb y hy hyC).2
    linarith
  have hjump :=
    AvramDividend.Classical.avram_sweep16_20261106_original_right_payment_secant_from_gradient
      X x C hC hxc D hD w hw_cont hw_smooth hgrad
  obtain ⟨M, G, H, hMI, hGI, hHI, hMzero, hMz, hGz, hHz, hGH, hPos⟩ :=
    AvramDividend.Classical.avram_jump6_B_original_positive_clock_stopped_signed_Ito_source_only
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_hjb
      x hx hxc D hD hxpos k hk τ hτeq hτmeas hτstop
      W Cash Term hW hCash hTerm hCashI
  refine ⟨M, G, H, hMI, hGI, hHI, hMzero, hGH, ?_⟩
  filter_upwards [hMz, hGz, hHz, hPos] with ω hM hG hH hUpper
  by_cases hz : τ ω = 0
  · have hc :=
      AvramDividend.Classical.avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
        X x q w C D hD hjump τ W Cash Term hW hCash hTerm ω hz
    rw [hM hz, hG hz, hH hz]
    simpa only [add_zero] using hc
  · exact hUpper hz
