-- Prove2me | solution 1 for AvramDividend.Classical.dividendMeasure_Ioc_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T11:51:11.47311+00:00
-- url     : https://prove2.me/submissions/bb9dab58-27da-4c0d-b9ff-18c309e6786e

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_real_rightLim_measurable

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
    (a b : ℝ) :
    Measurable (fun ω => dividendMeasure D ω (Ioc a b)) := by
  have hmono : ∀ ω, Monotone (fun r : ℝ => D r.toNNReal ω) := by
    intro ω
    exact (hD.2.1 ω).comp Real.toNNReal_monotone
  have hmass : ∀ ω,
      dividendMeasure D ω (Ioc a b) =
        ENNReal.ofReal
          (Function.rightLim (fun r : ℝ => D r.toNNReal ω) b -
            Function.rightLim (fun r : ℝ => D r.toNNReal ω) a) := by
    intro ω
    unfold dividendMeasure
    rw [dif_pos (hmono ω), StieltjesFunction.measure_Ioc,
      Monotone.stieltjesFunction_eq, Monotone.stieltjesFunction_eq]
  simp_rw [hmass]
  exact
    ((dividendStrategy_real_rightLim_measurable D hD b).sub
      (dividendStrategy_real_rightLim_measurable D hD a)).ennreal_ofReal
