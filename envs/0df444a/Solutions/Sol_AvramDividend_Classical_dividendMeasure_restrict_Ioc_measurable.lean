-- Prove2me | solution 1 for AvramDividend.Classical.dividendMeasure_restrict_Ioc_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T13:41:29.555188+00:00
-- url     : https://prove2.me/submissions/db2588cc-ff88-47b1-8c54-e5fc532b10fd

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (l u : ℝ) :
    Measurable (fun ω => (dividendMeasure D ω).restrict (Ioc l u)) := by
  let μ : Ω → Measure ℝ :=
    fun ω => (dividendMeasure D ω).restrict (Ioc l u)
  have hmono : ∀ ω, Monotone (fun r : ℝ => D r.toNNReal ω) := by
    intro ω
    exact (hD.2.1 ω).comp Real.toNNReal_monotone
  letI hfinite : ∀ ω, IsFiniteMeasure (μ ω) := fun ω => by
    rw [MeasureTheory.isFiniteMeasure_restrict]
    unfold dividendMeasure
    rw [dif_pos (hmono ω), StieltjesFunction.measure_Ioc,
      Monotone.stieltjesFunction_eq, Monotone.stieltjesFunction_eq]
    exact ENNReal.ofReal_ne_top
  change Measurable μ
  refine Measurable.measure_of_isPiSystem
    (S := {s : Set ℝ | ∃ a b : ℝ, a < b ∧ Ioc a b = s})
    (borel_eq_generateFrom_Ioc ℝ) (isPiSystem_Ioc id id) ?_ ?_
  · intro s hs
    rcases hs with ⟨a, b, hab, rfl⟩
    have hIoc : MeasurableSet (Ioc a b) := measurableSet_Ioc
    change Measurable
      (fun ω => ((dividendMeasure D ω).restrict (Ioc l u)) (Ioc a b))
    simp_rw [Measure.restrict_apply hIoc, Set.Ioc_inter_Ioc]
    exact dividendMeasure_Ioc_measurable D hD (max a l) (min b u)
  · change Measurable
      (fun ω => ((dividendMeasure D ω).restrict (Ioc l u)) Set.univ)
    simp_rw [Measure.restrict_apply_univ]
    exact dividendMeasure_Ioc_measurable D hD l u
