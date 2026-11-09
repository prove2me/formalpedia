-- Prove2me | solution 1 for BewleyGE.equation_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T10:42:07.498422+00:00
-- url     : https://prove2.me/submissions/507c2645-0ff0-4d9d-8d8c-af7a9216420a

import Mathlib
import Definitions.Def_BewleyGE_wealthOperator

open MeasureTheory

open BewleyGE in
theorem solution {n : ℕ} (E : Economy n) (p : Fin n → ℝ) (r : ℝ) (hp : ∀ i, 0 < p i)
    (hr0 : 0 < r) (hr1 : r < 1) (g : ℝ → ℝ) (hg : Measurable g) (ν : Measure ℝ)
    (hν : IsProbabilityMeasure ν) (f : ℝ → ℝ) (hf : Measurable f)
    (hfb : ∃ C : ℝ, ∀ a, |f a| ≤ C) :
    ∫ a, f a ∂(wealthOperator E p r g ν) =
      ∫ a, ∑ y ∈ E.Y, E.e y * f ((1 + r) * g a + ∑ i, p i * y i) ∂ν := by
  haveI := hν
  obtain ⟨C, hC⟩ := hfb
  have hT : ∀ y : Fin n → ℝ, Measurable (fun a => (1 + r) * g a + ∑ i, p i * y i) :=
    fun y => (measurable_const.mul hg).add measurable_const
  have hfi : ∀ μ : Measure ℝ, IsFiniteMeasure μ → Integrable f μ := by
    intro μ _
    exact Integrable.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun a => by rw [Real.norm_eq_abs]; exact hC a))
  have hcomp : ∀ y : Fin n → ℝ,
      Integrable (fun a => f ((1 + r) * g a + ∑ i, p i * y i)) ν := by
    intro y
    exact Integrable.of_bound (hf.comp (hT y)).aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun a => by rw [Real.norm_eq_abs]; exact hC _))
  unfold wealthOperator
  rw [integral_finset_sum_measure (fun y _ =>
    (hfi _ (Measure.isFiniteMeasure_map _ _)).smul_measure ENNReal.ofReal_ne_top)]
  rw [integral_finsetSum _ (fun y _ => (hcomp y).const_mul (E.e y))]
  refine Finset.sum_congr rfl (fun y hy => ?_)
  rw [integral_smul_measure, integral_map (hT y).aemeasurable hf.aestronglyMeasurable,
    integral_const_mul, ENNReal.toReal_ofReal (E.e_pos y hy).le, smul_eq_mul]
