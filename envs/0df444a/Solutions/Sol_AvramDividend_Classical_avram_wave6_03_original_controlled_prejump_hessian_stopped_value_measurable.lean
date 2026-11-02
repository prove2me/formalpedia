-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_controlled_prejump_hessian_stopped_value_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:24:10.279569+00:00
-- url     : https://prove2.me/submissions/1c8da35c-d90b-467a-accb-af9263b7ccb5

import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_controlled_prejump_cap_hessian_stronglyPredictable

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) :
    Measurable[hτ.measurableSpace]
      (stoppedValue (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)
        (fun ω => (τ ω : WithTop ℝ≥0))) := by
  exact measurable_stoppedValue
    ((avram_wave5_03a_controlled_prejump_cap_hessian_stronglyPredictable
      X x D hD w C hw).isStronglyProgressive) hτ
