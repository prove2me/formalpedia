-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_true_preruin_original_full_stieltjes_reward_secant_diffuse_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:02:28.379967+00:00
-- url     : https://prove2.me/submissions/e15d06f6-4674-494a-8c9f-d6c8f3a623b1

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
/-- The *original* full stopped discounted Stieltjes dividend reward
at the true source-X ruin clock is bounded by actual chronological jump
secants and an automatically decomposed atomless dividend measure.
Only the corrected pre-ruin-or-zero HJump hypothesis is required. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (T : ℝ≥0) (q : ℝ)
    (hloc : ∀ t : ℝ≥0, t ≤ T →
      (t : ℝ) ∈ paymentTimes (ruinTime X x D ω) →
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
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-q * s)) ∂dividendMeasure D ω) ≤
      (∑' t : A,
        ENNReal.ofReal
          (w (riskProcess X x D (t : ℝ).toNNReal ω) -
            w (riskProcess X x D (t : ℝ).toNNReal ω -
              (rightLimit D (t : ℝ).toNNReal ω -
                D (t : ℝ).toNNReal ω))) *
        (paymentTimes (ruinTime X x D ω)).indicator
          (fun s : ℝ => ENNReal.ofReal (Real.exp (-q * s))) (t : ℝ)) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-q * s)) *
          ENNReal.ofReal (deriv w (riskProcess X x D s.toNNReal ω))
          ∂μdiffuse) := by
  dsimp only
  have hJumpWindow : ∀ t : ℝ≥0, t ≤ T →
      (t : ℝ) ∈ paymentTimes (ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) := by
    intro t _ hp
    change (t : ℝ) ∈ Ici (0 : ℝ) ∩
      ({0} ∪ {u : ℝ | ENNReal.ofReal u < ruinTime X x D ω}) at hp
    apply hjump t
    rcases hp.2 with hzero | hlt
    · left
      have hz : (t : ℝ) = 0 := hzero
      exact_mod_cast hz
    · right
      have hReal : ENNReal.ofReal (t : ℝ) < ruinTime X x D ω := hlt
      simpa only [ENNReal.ofReal_coe_nnreal] using hReal
  exact
    avram_wave4_04b_original_stopped_full_stieltjes_control_correction
      X x D hD w C hw_grad ω T (ruinTime X x D ω) q
      hloc hJumpWindow
