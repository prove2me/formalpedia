-- Prove2me | solution 1 for AvramDividend.Classical.killed_survival_joint_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:41:56.673+00:00
-- url     : https://prove2.me/submissions/74375cba-ebff-46cc-8551-05a1e4e5efb0

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_joint_reserve_closed_survival_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Tonelli exchanges capital and path integration for killed survival. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) (θ : ℝ) :
    (∫⁻ (x : ℝ), ∫⁻ (ω : Ω),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal (Real.exp (-θ * p.1)))
        (x, ω) ∂P ∂volume) =
    (∫⁻ (ω : Ω), ∫⁻ (x : ℝ),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal (Real.exp (-θ * p.1)))
        (x, ω) ∂volume ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hset : MeasurableSet {p : ℝ × Ω |
      0 < p.1 ∧ (∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2)} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (joint_reserve_closed_survival_measurable X t)
  have hexp : Measurable (fun p : ℝ × Ω =>
      ENNReal.ofReal (Real.exp (-θ * p.1))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_fst.const_mul (-θ)))
  have hf : Measurable (Set.indicator
      {p : ℝ × Ω | 0 < p.1 ∧
        ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
      (fun p : ℝ × Ω => ENNReal.ofReal (Real.exp (-θ * p.1)))) :=
    hexp.indicator hset
  exact lintegral_lintegral_swap hf.aemeasurable
