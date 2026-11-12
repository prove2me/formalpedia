-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_single_interval_charfun_disintegration_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T21:14:01.45794+00:00
-- url     : https://prove2.me/submissions/65107f34-90b3-4682-b1f5-f571a14f4fd2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_single_random_mark_interval_product_law_20261111
import Theorems.Thm_AvramDividend_Classical_avram_a06_charfun_product_measure_fubini_20261111
import Theorems.Thm_AvramDividend_Classical_avram_a06_measurable_random_mark_interval_20261111
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Finset
noncomputable section

/-- Scalar random-grid disintegration from a product-law and characteristic-function Fubini. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (N : Fin (n + 1) → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hN : Measurable (fun ω => fun i => N i ω))
    (hY : Measurable (fun ω => fun j => Y j ω))
    (hSeparate : IndepFun (fun ω => fun i => N i ω)
      (fun ω => fun j => Y j ω) P)
    (i : Fin n) (t : ℝ) :
    MeasureTheory.charFun
      (Measure.map (fun ω : Ω =>
        ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω) P) t =
    ∫ ω, MeasureTheory.charFun
      (Measure.map (fun ω' : Ω =>
        ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω') P) t ∂P := by
  let X : Ω → Fin (n + 1) → ℕ := fun ω j => N j ω
  let Z : Ω → ℕ → ℝ := fun ω j => Y j ω
  let S : ((Fin (n + 1) → ℕ) × (ℕ → ℝ)) → ℝ :=
    fun p => ∑ j ∈ Finset.Ico (p.1 i.castSucc) (p.1 i.succ), p.2 j
  have hA : Measurable (fun p : (Fin (n + 1) → ℕ) × (ℕ → ℝ) =>
      p.1 i.castSucc) := (measurable_pi_apply i.castSucc).comp measurable_fst
  have hB : Measurable (fun p : (Fin (n + 1) → ℕ) × (ℕ → ℝ) =>
      p.1 i.succ) := (measurable_pi_apply i.succ).comp measurable_fst
  have hS : Measurable S :=
    AvramDividend.Classical.avram_a06_measurable_random_mark_interval_20261111
      (fun (p : (Fin (n + 1) → ℕ) × (ℕ → ℝ)) => p.1 i.castSucc) (fun (p : (Fin (n + 1) → ℕ) × (ℕ → ℝ)) => p.1 i.succ)
      (fun j (p : (Fin (n + 1) → ℕ) × (ℕ → ℝ)) => p.2 j) hA hB
      (fun j => (measurable_pi_apply j).comp measurable_snd)
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
      congrArg (fun Q : Measure ℝ => MeasureTheory.charFun Q t)
        (Measure.map_map (hm m) hY)
  have hK : AEStronglyMeasurable
      (fun m => MeasureTheory.charFun (Measure.map (fun z => S (m,z)) ν) t) μ := by
    let F : ((Fin (n + 1) → ℕ) × (ℕ → ℝ)) → ℂ :=
      fun p => Complex.exp ((↑(t * S p) : ℂ) * Complex.I)
    have hFm : Measurable F := by dsimp [F]; fun_prop
    have hFi : Integrable F (μ.prod ν) := by
      refine Integrable.of_bound hFm.aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun p => ?_))
      simp only [F, Complex.norm_exp_ofReal_mul_I, le_refl]
    have hK' : ∀ m, MeasureTheory.charFun
        (Measure.map (fun z => S (m,z)) ν) t = ∫ z, F (m,z) ∂ν := by
      intro m
      rw [charFun_apply_real, integral_map (hm m).aemeasurable (by fun_prop)]
      simp only [F, Complex.ofReal_mul]
    simpa only [hK'] using hFi.integral_prod_left.aestronglyMeasurable
  calc
    MeasureTheory.charFun (Measure.map (fun ω => S (X ω,Z ω)) P) t =
        MeasureTheory.charFun (Measure.map S (μ.prod ν)) t := by
      rw [AvramDividend.Classical.avram_a06_single_random_mark_interval_product_law_20261111
        P n N Y hN hY hSeparate i]
    _ = ∫ m, MeasureTheory.charFun (Measure.map (fun z => S (m,z)) ν) t ∂μ :=
      AvramDividend.Classical.avram_a06_charfun_product_measure_fubini_20261111
        μ ν S hS t
    _ = ∫ ω, MeasureTheory.charFun
          (Measure.map (fun z => S (X ω,z)) ν) t ∂P :=
      integral_map hN.aemeasurable hK
    _ = ∫ ω, MeasureTheory.charFun
          (Measure.map (fun ω' => S (X ω,Z ω')) P) t ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact hFixed (X ω)