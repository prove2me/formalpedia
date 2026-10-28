-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_weighted_killed_survival_joint_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:47:43.466943+00:00
-- url     : https://prove2.me/submissions/611255bd-2ed2-4d10-bbe6-25057d153b84

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_joint_reserve_closed_survival_measurable
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (β θ : ℝ) :
    (∫⁻ (x : ℝ), ∫⁻ (ω : Ω),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal
          (Real.exp (-β * p.1) *
            Real.exp (θ * X.X t p.2 -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))
        (x, ω) ∂P ∂volume) =
    (∫⁻ (ω : Ω), ∫⁻ (x : ℝ),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal
          (Real.exp (-β * p.1) *
            Real.exp (θ * X.X t p.2 -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))
        (x, ω) ∂volume ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hset : MeasurableSet {p : ℝ × Ω |
      0 < p.1 ∧ (∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2)} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (joint_reserve_closed_survival_measurable X t)
  have hXt : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hweight : Measurable (fun p : ℝ × Ω =>
      Real.exp (θ * X.X t p.2 -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) :=
    Real.measurable_exp.comp
      (((hXt.comp measurable_snd).const_mul θ).sub measurable_const)
  have hcapital : Measurable (fun p : ℝ × Ω => Real.exp (-β * p.1)) :=
    Real.measurable_exp.comp (measurable_fst.const_mul (-β))
  have hkernel : Measurable (fun p : ℝ × Ω => ENNReal.ofReal
      (Real.exp (-β * p.1) *
        Real.exp (θ * X.X t p.2 -
          (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))) :=
    ENNReal.measurable_ofReal.comp (hcapital.mul hweight)
  have hf : Measurable (Set.indicator
      {p : ℝ × Ω | 0 < p.1 ∧
        ∀ s : ℝ≥0, s ≤ t → 0 ≤ p.1 + X.X s p.2}
      (fun p : ℝ × Ω => ENNReal.ofReal
        (Real.exp (-β * p.1) *
          Real.exp (θ * X.X t p.2 -
            (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)))) :=
    hkernel.indicator hset
  exact lintegral_lintegral_swap hf.aemeasurable
