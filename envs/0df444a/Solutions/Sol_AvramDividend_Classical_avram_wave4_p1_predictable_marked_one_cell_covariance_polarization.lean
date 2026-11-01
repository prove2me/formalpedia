-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_predictable_marked_one_cell_covariance_polarization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:34:30.170737+00:00
-- url     : https://prove2.me/submissions/83f354ca-f9df-415e-94e7-3faa6d4f3e9e

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_weighted_marked_poisson_l2_isometry

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped ENNReal NNReal Nat

/-- Polarization of genuine marked-Poisson predictably weighted cell energy:
the mixed compensated product is integrable, with covariance determined
by the three mark-kernel squared energies. -/
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
        (∫ ω, H ω ^ 2 ∂μ) * ((r : ℝ) / 2) *
          ((∫ z, (f z + g z) ^ 2 ∂ν) -
            (∫ z, f z ^ 2 ∂ν) - (∫ z, g z ^ 2 ∂ν)) := by
  let A : Ω → ℝ := fun ω => H ω *
    ((∑ n ∈ Finset.range (K ω), f (Y n ω)) -
      (r : ℝ) * ∫ z, f z ∂ν)
  let B : Ω → ℝ := fun ω => H ω *
    ((∑ n ∈ Finset.range (K ω), g (Y n ω)) -
      (r : ℝ) * ∫ z, g z ∂ν)
  let C : Ω → ℝ := fun ω => H ω *
    ((∑ n ∈ Finset.range (K ω), (f (Y n ω) + g (Y n ω))) -
      (r : ℝ) * ∫ z, f z + g z ∂ν)
  change Integrable (fun ω => A ω * B ω) μ ∧
    (∫ ω, A ω * B ω ∂μ) =
      (∫ ω, H ω ^ 2 ∂μ) * ((r : ℝ) / 2) *
        ((∫ z, (f z + g z) ^ 2 ∂ν) -
          (∫ z, f z ^ 2 ∂ν) - (∫ z, g z ^ 2 ∂ν))
  have hA := avram_wave4_p1_predictable_weighted_marked_poisson_l2_isometry
    μ ν H hHm hH2 K Y hKm r hKlaw hYm hYL hYi
    hCountMarks hPast f hf hfI hf2
  have hB := avram_wave4_p1_predictable_weighted_marked_poisson_l2_isometry
    μ ν H hHm hH2 K Y hKm r hKlaw hYm hYL hYi
    hCountMarks hPast g hg hgI hg2
  have hC := avram_wave4_p1_predictable_weighted_marked_poisson_l2_isometry
    μ ν H hHm hH2 K Y hKm r hKlaw hYm hYL hYi
    hCountMarks hPast (fun z => f z + g z)
    (hf.add hg) (hfI.add hgI) (hf2.add hg2)
  have hMarkAdd : (∫ z, f z + g z ∂ν) =
      (∫ z, f z ∂ν) + (∫ z, g z ∂ν) := by
    simpa only [Pi.add_apply] using integral_add hfI hgI
  have hCadd : ∀ ω, C ω = A ω + B ω := by
    intro ω
    dsimp [A, B, C]
    rw [Finset.sum_add_distrib, hMarkAdd]
    ring
  have hProdEq : (fun ω => A ω * B ω) =
      (fun ω => (1 / 2 : ℝ) * ((C ω ^ 2 - A ω ^ 2) - B ω ^ 2)) := by
    funext ω
    rw [hCadd ω]
    ring
  have hProdInt : Integrable
      (fun ω => (1 / 2 : ℝ) * ((C ω ^ 2 - A ω ^ 2) - B ω ^ 2)) μ := by
    exact ((hC.1.sub hA.1).sub hB.1).const_mul _
  have hSubCA : (∫ ω, C ω ^ 2 - A ω ^ 2 ∂μ) =
      (∫ ω, C ω ^ 2 ∂μ) - (∫ ω, A ω ^ 2 ∂μ) := by
    simpa only [Pi.sub_apply] using integral_sub hC.1 hA.1
  have hSubCAB :
      (∫ ω, (C ω ^ 2 - A ω ^ 2) - B ω ^ 2 ∂μ) =
      (∫ ω, C ω ^ 2 - A ω ^ 2 ∂μ) -
        (∫ ω, B ω ^ 2 ∂μ) := by
    simpa only [Pi.sub_apply] using integral_sub (hC.1.sub hA.1) hB.1
  constructor
  · rw [hProdEq]
    exact hProdInt
  · calc
      (∫ ω, A ω * B ω ∂μ) =
        (∫ ω, (1 / 2 : ℝ) *
          ((C ω ^ 2 - A ω ^ 2) - B ω ^ 2) ∂μ) := by
            rw [hProdEq]
      _ = (1 / 2 : ℝ) *
          ((∫ ω, C ω ^ 2 ∂μ) -
            (∫ ω, A ω ^ 2 ∂μ) - (∫ ω, B ω ^ 2 ∂μ)) := by
          rw [integral_const_mul, hSubCAB, hSubCA]
      _ = (∫ ω, H ω ^ 2 ∂μ) * ((r : ℝ) / 2) *
          ((∫ z, (f z + g z) ^ 2 ∂ν) -
            (∫ z, f z ^ 2 ∂ν) - (∫ z, g z ^ 2 ∂ν)) := by
          rw [hC.2, hA.2, hB.2]
          ring
