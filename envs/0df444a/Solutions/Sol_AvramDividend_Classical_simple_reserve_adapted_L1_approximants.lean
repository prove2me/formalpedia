-- Prove2me | solution 1 for AvramDividend.Classical.simple_reserve_adapted_L1_approximants
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T20:32:48.210998+00:00
-- url     : https://prove2.me/submissions/6d4100f7-feac-40d8-9292-f9261fa61320



import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_simple_reserve_approxOn_preserves_adaptedness
import Theorems.Thm_AvramDividend_Classical_simple_reserve_approxOn_real_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (s : ℝ≥0) (Z : Ω → ℝ)
    (hZ : Measurable[𝓕 s] Z)
    (hZm : Measurable Z) (hI : Integrable Z P) :
    (∀ n : ℕ, Measurable[𝓕 s] (fun ω =>
      (SimpleFunc.approxOn Z hZm (Set.range Z ∪ {0}) 0
        (by simp) n) ω)) ∧
    Tendsto (fun n : ℕ =>
      ∫ ω, |(SimpleFunc.approxOn Z hZm
          (Set.range Z ∪ {0}) 0 (by simp) n) ω - Z ω| ∂P)
      atTop (nhds 0) := by
  constructor
  · intro n
    exact AvramDividend.Classical.simple_reserve_approxOn_preserves_adaptedness
      (mΩ := mΩ) (𝓕 s) Z hZ hZ (Set.range Z ∪ {0}) 0 (by simp) n
  · exact AvramDividend.Classical.simple_reserve_approxOn_real_L1
      P Z hZm hI


