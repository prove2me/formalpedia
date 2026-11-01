-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_preruin_localised_original_stieltjes_reward_full_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:02:31.933789+00:00
-- url     : https://prove2.me/submissions/6b77b9b0-04ea-4997-9fb8-b720cb9a9881

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_original_stopped_full_stieltjes_control_correction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section
/-- A genuine pre-ruin/localisation stop inherits the complete original
Stieltjes dividend bound, using the corrected global HJump premise and
the actual atomless Stieltjes residual. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (T : ℝ≥0) (τ : ℝ≥0∞)
    (hτ : τ ≤ ruinTime X x D ω) (q : ℝ)
    (hloc : ∀ t : ℝ≥0, t ≤ T →
      (t : ℝ) ∈ paymentTimes τ →
      0 < riskProcess X x D t ω ∧
        ENNReal.ofReal (riskProcess X x D t ω) < C)
    (hjump : ∀ t : ℝ≥0,
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧ NullSingletonClass μdiffuse ∧
      (∫⁻ s in paymentTimes τ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-q * s)) ∂dividendMeasure D ω) ≤
      (∑' t : A,
        ENNReal.ofReal
          (w (riskProcess X x D (t : ℝ).toNNReal ω) -
            w (riskProcess X x D (t : ℝ).toNNReal ω -
              (rightLimit D (t : ℝ).toNNReal ω -
                D (t : ℝ).toNNReal ω))) *
        (paymentTimes τ).indicator
          (fun s : ℝ => ENNReal.ofReal (Real.exp (-q * s))) (t : ℝ)) +
      (∫⁻ s in paymentTimes τ,
        ENNReal.ofReal (Real.exp (-q * s)) *
          ENNReal.ofReal (deriv w (riskProcess X x D s.toNNReal ω))
          ∂μdiffuse) := by
  dsimp only
  have hJumpWindow : ∀ t : ℝ≥0, t ≤ T →
      (t : ℝ) ∈ paymentTimes τ →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) := by
    intro t _ hp
    change (t : ℝ) ∈ Ici (0 : ℝ) ∩
      ({0} ∪ {u : ℝ | ENNReal.ofReal u < τ}) at hp
    apply hjump t
    rcases hp.2 with hzero | hlt
    · left
      have hz : (t : ℝ) = 0 := hzero
      exact_mod_cast hz
    · right
      have hReal : ENNReal.ofReal (t : ℝ) < τ := hlt
      have hBefore : (t : ℝ≥0∞) < τ := by
        simpa only [ENNReal.ofReal_coe_nnreal] using hReal
      exact lt_of_lt_of_le hBefore hτ
  exact
    avram_wave4_04b_original_stopped_full_stieltjes_control_correction
      X x D hD w C hw_grad ω T τ q hloc hJumpWindow
