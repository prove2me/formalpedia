-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_predictable_marked_one_cell_bilinear_covariance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:45:16.957051+00:00
-- url     : https://prove2.me/submissions/4198f1a0-2d76-4f62-843d-4a2ee7ee3efa

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_marked_one_cell_covariance_polarization

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat

/-- The compensated marked-Poisson covariance is the mark L² inner
product times the predictable past-weight energy. -/
theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (H : Ω → ℝ) (hHm : Measurable H)
    (hH2 : Integrable (fun ω => H ω ^ 2) μ)
    (K : Ω → ℕ) (Y : ℕ → Ω → E)
    (hKm : Measurable K) (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) μ)
    (hYm : ∀ n, Measurable (Y n)) (hYL : ∀ n, HasLaw (Y n) ν μ)
    (hYi : iIndepFun Y μ)
    (hCountMarks : IndepFun K (fun ω (n : ℕ) => Y n ω) μ)
    (hPast : IndepFun H (fun ω => (K ω, fun n : ℕ => Y n ω)) μ)
    (f g : E → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfI : Integrable f ν) (hgI : Integrable g ν)
    (hf2 : MemLp f 2 ν) (hg2 : MemLp g 2 ν) :
    let A : Ω → ℝ := fun ω => H ω *
      ((∑ n ∈ Finset.range (K ω), f (Y n ω)) -
        (r : ℝ) * ∫ z, f z ∂ν)
    let B : Ω → ℝ := fun ω => H ω *
      ((∑ n ∈ Finset.range (K ω), g (Y n ω)) -
        (r : ℝ) * ∫ z, g z ∂ν)
    Integrable (fun ω => A ω * B ω) μ ∧
      (∫ ω, A ω * B ω ∂μ) =
        (∫ ω, H ω ^ 2 ∂μ) * (r : ℝ) * (∫ z, f z * g z ∂ν) := by
  let A : Ω → ℝ := fun ω => H ω *
    ((∑ n ∈ Finset.range (K ω), f (Y n ω)) -
      (r : ℝ) * ∫ z, f z ∂ν)
  let B : Ω → ℝ := fun ω => H ω *
    ((∑ n ∈ Finset.range (K ω), g (Y n ω)) -
      (r : ℝ) * ∫ z, g z ∂ν)
  change Integrable (fun ω => A ω * B ω) μ ∧
    (∫ ω, A ω * B ω ∂μ) =
      (∫ ω, H ω ^ 2 ∂μ) * (r : ℝ) * (∫ z, f z * g z ∂ν)
  have hP := avram_wave4_p1_predictable_marked_one_cell_covariance_polarization
    μ ν H hHm hH2 K Y hKm r hKlaw hYm hYL hYi
    hCountMarks hPast f g hf hg hfI hgI hf2 hg2
  have hfgI : Integrable (fun z => f z * g z) ν := by
    have h := hf2.integrable_mul hg2
    have hEq : (fun z => f z * g z) = f * g := by
      funext z
      rfl
    rw [hEq]
    exact h
  have hfSqI : Integrable (fun z => f z ^ 2) ν :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf2
  have hgSqI : Integrable (fun z => g z ^ 2) ν :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).1 hg2
  have hfg2I : Integrable (fun z => (2 : ℝ) * (f z * g z)) ν :=
    hfgI.const_mul 2
  have hOuter :
      (∫ z, (f z ^ 2 + (2 : ℝ) * (f z * g z)) + g z ^ 2 ∂ν) =
      (∫ z, f z ^ 2 + (2 : ℝ) * (f z * g z) ∂ν) +
        (∫ z, g z ^ 2 ∂ν) := by
    simpa only [Pi.add_apply] using integral_add (hfSqI.add hfg2I) hgSqI
  have hInner :
      (∫ z, f z ^ 2 + (2 : ℝ) * (f z * g z) ∂ν) =
      (∫ z, f z ^ 2 ∂ν) +
        (∫ z, (2 : ℝ) * (f z * g z) ∂ν) := by
    simpa only [Pi.add_apply] using integral_add hfSqI hfg2I
  have hMark :
      (∫ z, (f z + g z) ^ 2 ∂ν) =
      (∫ z, f z ^ 2 ∂ν) +
        2 * (∫ z, f z * g z ∂ν) +
          (∫ z, g z ^ 2 ∂ν) := by
    calc
      _ = (∫ z, (f z ^ 2 + (2 : ℝ) * (f z * g z)) +
          g z ^ 2 ∂ν) := by
            apply integral_congr_ae
            filter_upwards [] with z
            ring
      _ = _ := by
            rw [hOuter, hInner, integral_const_mul]
  constructor
  · exact hP.1
  · calc
      (∫ ω, A ω * B ω ∂μ) =
        (∫ ω, H ω ^ 2 ∂μ) * ((r : ℝ) / 2) *
          ((∫ z, (f z + g z) ^ 2 ∂ν) -
            (∫ z, f z ^ 2 ∂ν) - (∫ z, g z ^ 2 ∂ν)) := hP.2
      _ = (∫ ω, H ω ^ 2 ∂μ) * (r : ℝ) *
          (∫ z, f z * g z ∂ν) := by
            rw [hMark]
            ring
