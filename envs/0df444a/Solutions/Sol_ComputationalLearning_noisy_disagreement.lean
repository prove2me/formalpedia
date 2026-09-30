-- Prove2me | solution 1 for ComputationalLearning.noisy_disagreement
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:23:06.602038+00:00
-- url     : https://prove2.me/submissions/263eada4-82a6-438f-a871-7f777e287584

import Mathlib
import Definitions.Def_ComputationalLearning_Noise

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

open ComputationalLearning MeasureTheory ProbabilityTheory in
theorem solution {X : Type*} [MeasurableSpace X] (D : Measure X)
    [IsProbabilityMeasure D] (c h : X → Bool) (hc : Measurable c) (hh : Measurable h) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (noisyExampleLaw D c η {p | h p.1 ≠ p.2}).toReal = η + (1 - 2 * η) * errorOf D c h := by
  have hS : MeasurableSet {p : X × Bool | h p.1 ≠ p.2} :=
    (measurableSet_eq_fun (hh.comp measurable_fst) measurable_snd).compl
  have hnot : Measurable (fun x : X ↦ !c x) :=
    (measurable_of_countable (fun b : Bool ↦ !b)).comp hc
  have hf : Measurable (fun p : X × Bool ↦ (p.1, if p.2 then !c p.1 else c p.1)) := by
    refine measurable_fst.prodMk ?_
    exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
      (hnot.comp measurable_fst) (hc.comp measurable_fst)
  have hpre : MeasurableSet
      ((fun p : X × Bool ↦ (p.1, if p.2 then !c p.1 else c p.1)) ⁻¹' {p | h p.1 ≠ p.2}) :=
    hf hS
  have hA : MeasurableSet {x | h x ≠ c x} := (measurableSet_eq_fun hh hc).compl
  have eT : (fun x : X ↦ (x, true)) ⁻¹'
      ((fun p : X × Bool ↦ (p.1, if p.2 then !c p.1 else c p.1)) ⁻¹' {p | h p.1 ≠ p.2})
      = {x | h x ≠ c x}ᶜ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_compl_iff, if_true]
    show h x ≠ !c x ↔ ¬ (h x ≠ c x)
    generalize h x = a
    generalize c x = b
    cases a <;> cases b <;> simp
  have eF : (fun x : X ↦ (x, false)) ⁻¹'
      ((fun p : X × Bool ↦ (p.1, if p.2 then !c p.1 else c p.1)) ⁻¹' {p | h p.1 ≠ p.2})
      = {x | h x ≠ c x} := by
    ext x
    simp
  have key : noisyExampleLaw D c η {p | h p.1 ≠ p.2}
      = ENNReal.ofReal η * (1 - D {x | h x ≠ c x})
        + ENNReal.ofReal (1 - η) * D {x | h x ≠ c x} := by
    unfold noisyExampleLaw ComputationalLearning.bernoulliMeasure
    rw [Measure.map_apply hf hS, Measure.prod_add, Measure.prod_smul_right,
      Measure.prod_smul_right, Measure.prod_dirac, Measure.prod_dirac,
      Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.map_apply measurable_prodMk_right hpre,
      Measure.map_apply measurable_prodMk_right hpre, eT, eF, prob_compl_eq_one_sub hA]
    simp only [smul_eq_mul]
  rw [key, ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hη0, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
  unfold errorOf
  ring
