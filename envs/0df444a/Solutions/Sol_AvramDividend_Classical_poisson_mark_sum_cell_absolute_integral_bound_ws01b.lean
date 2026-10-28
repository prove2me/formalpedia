-- Prove2me | solution 1 for AvramDividend.Classical.poisson_mark_sum_cell_absolute_integral_bound_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:03:20.027504+00:00
-- url     : https://prove2.me/submissions/9ee2d219-239b-4a5f-a48f-b3ac76d0ae94

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_independent_count_cell_mark_mean_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat

/-- A genuinely integrable Poisson count cell controls the absolute
random-mark sum by the mean absolute mark times count-cell mass. -/
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K)
    (hYm : ∀ n, Measurable (Y n))
    (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hIndep : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (j : ℕ) (f : E → ℝ) (hf : Measurable f)
    (hfI : Integrable f ν) :
    (∫ ω in {ω | K ω = j},
      |∑ n ∈ Finset.range (K ω), f (Y n ω)| ∂μ) ≤
      μ.real {ω | K ω = j} *
        ((j : ℝ) * ∫ y, |f y| ∂ν) := by
  let s : Set Ω := {ω | K ω = j}
  have hs : MeasurableSet s :=
    hKm (measurableSet_singleton j)
  have hFixed (g : E → ℝ) (hg : Measurable g)
      (hgI : Integrable g ν) :
      Integrable (fun ω => ∑ n ∈ Finset.range j, g (Y n ω)) μ := by
    refine integrable_finsetSum _ fun n hn => ?_
    have hI : Integrable g (Measure.map (Y n) μ) := by
      rwa [(hYL n).map_eq]
    exact hI.comp_measurable (hYm n)
  have hEq : Set.EqOn
      (fun ω => ∑ n ∈ Finset.range (K ω), f (Y n ω))
      (fun ω => ∑ n ∈ Finset.range j, f (Y n ω)) s := by
    intro ω hω
    change K ω = j at hω
    exact congrArg
      (fun m : ℕ => ∑ n ∈ Finset.range m, f (Y n ω)) hω
  have hInt :
      IntegrableOn
        (fun ω => ∑ n ∈ Finset.range (K ω), f (Y n ω)) s μ :=
    ((hFixed f hf hfI).integrableOn).congr_fun
      hEq.symm hs
  have hbound :
      (∫ ω in s, |∑ n ∈ Finset.range (K ω), f (Y n ω)| ∂μ) ≤
        (∫ ω in s,
          ∑ n ∈ Finset.range j, |f (Y n ω)| ∂μ) := by
    refine setIntegral_mono_on hInt.norm
      ((hFixed (fun y => |f y|) hf.abs hfI.abs).integrableOn)
      hs ?_
    intro ω hω
    have hKω : K ω = j := hω
    rw [hKω]
    exact Finset.abs_sum_le_sum_abs _ _
  calc
    (∫ ω in s,
      |∑ n ∈ Finset.range (K ω), f (Y n ω)| ∂μ) ≤
        (∫ ω in s,
          ∑ n ∈ Finset.range j, |f (Y n ω)| ∂μ) := hbound
    _ = μ.real s * ((j : ℝ) * ∫ y, |f y| ∂ν) := by
      simpa only [s] using
        poisson_independent_count_cell_mark_mean_ws01b
          μ ν K Y hKm hYm hYL hIndep j
          (fun y => |f y|) hf.abs hfI.abs
