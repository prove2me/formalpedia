-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_original_uniform_prefix_positive_masked_expected_upper_only
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:27:10.917952+00:00
-- url     : https://prove2.me/submissions/5adb4b0f-3619-4204-81b8-5e89020f320f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_uniform_prefix_positive_clock_excess_signed_budget
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_compact_original_reward_L1_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_masked_mean_budget_iff_positive_clock_excess_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The positive-clock signed excess is the exact probability-normalised masked budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P) (hinfinite : C = ⊤) :
    ∀ k, ∀ (κ : ℕ → Ω → ℝ≥0)
      (hκstop : ∀ j, IsStoppingTime 𝓕.rightCont
        (fun ω => (κ j ω : WithTop ℝ≥0)))
      (hκle : ∀ j ω, κ j ω ≤ σ k ω)
      (hκprefix : ∀ j ω (t : ℝ≥0), t ≤ κ j ω → X.X t ω ≤ (j : ℝ) + 1)
      (H : ℕ → Ω → ℝ),
      (∀ j ω, H j ω =
        Real.exp (-(q * (κ j ω : ℝ))) *
          w (if κ j ω = 0 ∨ (κ j ω : ℝ≥0∞) < ruinTime X x D ω then
              x + X.X (κ j ω) ω - rightLimit D (κ j ω) ω
            else riskProcess X x D (κ j ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ j ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) →
      ∀ j, (∫ ω, if κ j ω = 0 then w x else H j ω ∂P) ≤ w x 
:= by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k κ hκstop hκle hκprefix H hHsource j
  have hCashτI : Integrable (fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P := by
    have hEq : (fun ω =>
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) =
        Cash := funext (fun ω => (hCash ω).symm)
    rw [hEq]
    exact hCashI
  have hκτ : ∀ i ω, κ i ω ≤ τ ω := by
    intro i ω
    exact (hκle i ω).trans (hσle k ω)
  have hκbound : ∀ i ω, X.X (κ i ω) ω ≤ (i : ℝ) + 1 := by
    intro i ω
    exact hκprefix i ω (κ i ω) le_rfl
  have hHI : Integrable (H j) P :=
    (avram_ubv_top9_compact_original_reward_L1_nonnegative
      X hBV q (le_of_lt hq) w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD τ hCashτI κ hκstop hκτ hκbound H hHsource j).1
  let A : Set Ω := {ω | κ j ω = 0}
  have hA : MeasurableSet A :=
    avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
      𝓕 (κ j) (hκstop j)
  have hExcess : (∫ ω in Aᶜ, H j ω - w x ∂P) ≤ 0 :=
    avram_ubv_top9_original_uniform_prefix_positive_clock_excess_signed_budget
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop
      W Cash Term hW hCash hTerm hTermMeas hCashI
      σ F hσstop hσle hFsource hFI hinfinite
      k κ hκstop hκle hκprefix H hHsource j
  have hMask : (∫ ω, (if ω ∈ A then w x else H j ω) ∂P) ≤ w x :=
    (avram_p4_f12_masked_mean_budget_iff_positive_clock_excess_nonpositive
      P A hA (H j) hHI (w x)).2 hExcess
  change (∫ ω, if κ j ω = 0 then w x else H j ω ∂P) ≤ w x at hMask
  exact hMask
