-- Prove2me | solution 1 for AvramDividend.Classical.levy_finiteStopping_historyWeight_futureReward_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T16:45:17.863669+00:00
-- url     : https://prove2.me/submissions/7f58b1e2-0260-4ed7-aeef-3beb3786c074

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_restrictedFuturePath_mapLaw
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedSigma_indep_shiftedPath

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A stopping-history weight factors from future Lévy reward, evaluated on the original path law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (pastWeight : Ω → ℝ≥0∞)
    (hp : Measurable pastWeight)
    (hpPast : Measurable[
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] pastWeight)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞) (hr : Measurable reward) :
    (∫⁻ ω, pastWeight ω *
      reward (fun t : ℝ≥0 =>
        X.X (τ ω + t) ω - X.X (τ ω) ω) ∂P) =
      (∫⁻ ω, pastWeight ω ∂P) *
        (∫⁻ ω, reward (fun t : ℝ≥0 => X.X t ω) ∂P) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let hstop := isStoppingTime_withTop_of_le_events τ hτ
  let Y : Ω → (ℝ≥0 → ℝ) := fun ω t =>
    X.X (τ ω + t) ω - X.X (τ ω) ω
  let Z : Ω → (ℝ≥0 → ℝ) := fun ω t => X.X t ω
  have hY : Measurable Y :=
    levy_finiteStopping_stoppedFuturePath_measurable X τ hstop
  have hZ : Measurable Z := by
    apply measurable_pi_iff.mpr
    intro t
    exact (X.adapted t).mono (𝓕.le t) le_rfl
  have hUniv : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (Set.univ ∩ {ω : Ω | τ ω ≤ s}) := by
    intro s
    simpa only [Set.univ_inter] using hτ s
  have hFull : Measure.map Y P = Measure.map Z P := by
    simpa only [Y, Z, Measure.restrict_univ, measure_univ, one_smul] using
      (levy_finiteStopping_restrictedFuturePath_mapLaw
        X τ hstop Set.univ hUniv)
  have hRewardLaw :
      (∫⁻ ω, reward (Y ω) ∂P) =
        (∫⁻ ω, reward (Z ω) ∂P) := by
    rw [← lintegral_map hr hY, ← lintegral_map hr hZ, hFull]
  have hSigma : Indep hstop.measurableSpace
      (MeasurableSpace.comap Y inferInstance) P := by
    simpa only [hstop, Y] using
      (levy_finiteStopping_stoppedSigma_indep_shiftedPath X τ hτ)
  have hSmall : MeasurableSpace.comap pastWeight inferInstance ≤
      hstop.measurableSpace := hpPast.comap_le
  have hPair : IndepFun pastWeight Y P :=
    (IndepFun_iff_Indep pastWeight Y P).2
      (indep_of_indep_of_le_left hSigma hSmall)
  have hProduct : IndepFun pastWeight (reward ∘ Y) P :=
    hPair.comp measurable_id hr
  have hFactor :
      (∫⁻ ω, pastWeight ω * reward (Y ω) ∂P) =
        (∫⁻ ω, pastWeight ω ∂P) *
          (∫⁻ ω, reward (Y ω) ∂P) := by
    have hMul :=
      lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
        hp (hr.comp hY) hProduct
    simpa only [Pi.mul_apply, Function.comp_apply] using hMul
  simpa only [Y, Z] using hFactor.trans
    (congrArg (fun z : ℝ≥0∞ => (∫⁻ ω, pastWeight ω ∂P) * z) hRewardLaw)
