-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_random_grid_charfun_disintegrated_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T21:14:20.98332+00:00
-- url     : https://prove2.me/submissions/e5e5d556-5a3d-4f95-8ba3-09b5bfd27f78

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_random_grid_marked_vector_product_law_20261111
import Theorems.Thm_AvramDividend_Classical_avram_a06_vector_charfun_product_fubini_20261111
import Theorems.Thm_AvramDividend_Classical_avram_a06_joint_count_mark_grid_transform_measurable_20261111
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Finset
noncomputable section

/-- Vector Fourier disintegration from the independent product law and general Fubini. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (N : Fin (n + 1) → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable (fun ω => fun i => N i ω))
    (hY : Measurable (fun ω => fun j => Y j ω))
    (hSeparate : IndepFun (fun ω => fun i => N i ω)
      (fun ω => fun j => Y j ω) P)
    (t : WithLp 2 (Fin n → ℝ)) :
    MeasureTheory.charFun
      (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin n =>
        ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω)) P) t =
    ∫ ω, MeasureTheory.charFun
      (Measure.map (fun ω' : Ω => WithLp.toLp 2 (fun i : Fin n =>
        ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω')) P) t ∂P := by
  let X : Ω → Fin (n + 1) → ℕ := fun ω j => N j ω
  let Z : Ω → ℕ → ℝ := fun ω j => Y j ω
  let S : ((Fin (n + 1) → ℕ) × (ℕ → ℝ)) → WithLp 2 (Fin n → ℝ) :=
    fun p => WithLp.toLp 2 (fun i : Fin n =>
      ∑ j ∈ Finset.Ico (p.1 i.castSucc) (p.1 i.succ), p.2 j)
  have hS : Measurable S :=
    AvramDividend.Classical.avram_a06_joint_count_mark_grid_transform_measurable_20261111 n
  let μ : Measure (Fin (n + 1) → ℕ) := Measure.map X P
  let ν : Measure (ℕ → ℝ) := Measure.map Z P
  letI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hN.aemeasurable
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hm (m : Fin (n + 1) → ℕ) : Measurable (fun z : ℕ → ℝ => S (m,z)) :=
    hS.comp (measurable_const.prodMk measurable_id)
  have hFixed (m : Fin (n + 1) → ℕ) :
      MeasureTheory.charFun (Measure.map (fun z => S (m,z)) ν) t =
      MeasureTheory.charFun (Measure.map (fun ω => S (m,Z ω)) P) t := by
    simpa only [Function.comp_def] using
      congrArg (fun Q : Measure (WithLp 2 (Fin n → ℝ)) =>
        MeasureTheory.charFun Q t) (Measure.map_map (hm m) hY)
  have hK : AEStronglyMeasurable
      (fun m => MeasureTheory.charFun (Measure.map (fun z => S (m,z)) ν) t) μ := by
    let F : ((Fin (n + 1) → ℕ) × (ℕ → ℝ)) → ℂ :=
      fun p => Complex.exp ((↑(inner ℝ (S p) t) : ℂ) * Complex.I)
    have hFm : Measurable F := by dsimp [F]; fun_prop
    have hFi : Integrable F (μ.prod ν) := by
      refine Integrable.of_bound hFm.aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun p => ?_))
      simp only [F, Complex.norm_exp_ofReal_mul_I, le_refl]
    have hK' : ∀ m, MeasureTheory.charFun
        (Measure.map (fun z => S (m,z)) ν) t = ∫ z, F (m,z) ∂ν := by
      intro m
      rw [charFun_apply, integral_map (hm m).aemeasurable (by fun_prop)]

    simpa only [hK'] using hFi.integral_prod_left.aestronglyMeasurable
  calc
    MeasureTheory.charFun (Measure.map (fun ω => S (X ω,Z ω)) P) t =
        MeasureTheory.charFun (Measure.map S (μ.prod ν)) t := by
      rw [AvramDividend.Classical.avram_a06_random_grid_marked_vector_product_law_20261111
        P n X Z hN hY hSeparate]
    _ = ∫ m, MeasureTheory.charFun (Measure.map (fun z => S (m,z)) ν) t ∂μ :=
      AvramDividend.Classical.avram_a06_vector_charfun_product_fubini_20261111
        μ ν n S hS t
    _ = ∫ ω, MeasureTheory.charFun
          (Measure.map (fun z => S (X ω,z)) ν) t ∂P :=
      integral_map hN.aemeasurable hK
    _ = ∫ ω, MeasureTheory.charFun
          (Measure.map (fun ω' => S (X ω,Z ω')) P) t ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact hFixed (X ω)