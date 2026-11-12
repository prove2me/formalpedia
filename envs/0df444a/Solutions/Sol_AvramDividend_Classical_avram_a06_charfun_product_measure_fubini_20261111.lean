-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_charfun_product_measure_fubini_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:37:37.275908+00:00
-- url     : https://prove2.me/submissions/b30d7efa-20b2-409b-bf76-fa0c36988e58

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
noncomputable section

/-- Characteristic-function Fubini for a measurable image of a product probability law. -/
theorem solution
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : A × B → ℝ) (hf : Measurable f) (t : ℝ) :
    MeasureTheory.charFun (Measure.map f (μ.prod ν)) t =
      ∫ a, MeasureTheory.charFun (Measure.map (fun b => f (a,b)) ν) t ∂μ := by
  let F : A × B → ℂ := fun p =>
    Complex.exp ((↑(t * f p) : ℂ) * Complex.I)
  have hFm : Measurable F := by
    dsimp [F]
    fun_prop
  have hFi : Integrable F (μ.prod ν) := by
    refine Integrable.of_bound hFm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun p => ?_))
    simp only [F, Complex.norm_exp_ofReal_mul_I, le_refl]
  have hFibre (a : A) : Measurable (fun b : B => f (a,b)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  calc
    MeasureTheory.charFun (Measure.map f (μ.prod ν)) t =
        ∫ p, F p ∂(μ.prod ν) := by
      rw [charFun_apply_real, integral_map hf.aemeasurable (by fun_prop)]
      simp only [F, Complex.ofReal_mul]
    _ = ∫ a, ∫ b, F (a,b) ∂ν ∂μ :=
      integral_prod F hFi
    _ = ∫ a, MeasureTheory.charFun
          (Measure.map (fun b => f (a,b)) ν) t ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with a
      rw [charFun_apply_real,
        integral_map (hFibre a).aemeasurable (by fun_prop)]
      simp only [F, Complex.ofReal_mul]
