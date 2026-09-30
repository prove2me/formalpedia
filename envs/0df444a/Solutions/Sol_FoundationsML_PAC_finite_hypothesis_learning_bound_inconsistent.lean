-- Prove2me | solution 1 for FoundationsML.PAC.finite_hypothesis_learning_bound_inconsistent
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T22:45:16.865071+00:00
-- url     : https://prove2.me/submissions/b9e2fbac-e8c4-4775-9e5b-2e4d86b0a6d9

import Mathlib
import Definitions.Def_FoundationsML_PAC_GeneralizationError
import Definitions.Def_FoundationsML_PAC_EmpiricalError

open MeasureTheory

namespace FoundationsML.PAC

lemma pac_ge_not : GeneralizationError (Measure.dirac true) (fun x : Bool => x) (fun x => !x) = 1 := by
  unfold GeneralizationError
  have : {x : Bool | (!x) ≠ x} = Set.univ := by ext x; cases x <;> simp
  rw [this]; simp

lemma pac_emp_zero (S : Fin 0 → Bool) (c h : Bool → Bool) : EmpiricalError S c h = 0 := by
  unfold EmpiricalError; simp

lemma pac_set_empty (r : ℝ) :
    {S : Fin 0 → Bool | GeneralizationError (Measure.dirac true) (fun x : Bool => x) (fun x => !x) ≤
        EmpiricalError S (fun x : Bool => x) (fun x => !x) + Real.sqrt (r / (2 * ((0:ℕ):ℝ)))} = ∅ := by
  ext S
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
  rw [pac_ge_not, pac_emp_zero]
  simp

theorem single_dis : ¬ (∀ {X : Type} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (c h : X → Bool) (hc_meas : Measurable c) (hh_meas : Measurable h)
    (m : ℕ) (δ : ℝ) (hδ : 0 < δ),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | GeneralizationError D c h ≤
        EmpiricalError S c h + Real.sqrt (Real.log (2 / δ) / (2 * m))}).toReal) := by
  intro H
  have := H (Measure.dirac true) (fun x : Bool => x) (fun x => !x) measurable_id
    (measurable_from_top) 0 (1/2) (by norm_num)
  rw [pac_set_empty] at this
  simp at this
  norm_num at this

theorem finite_dis : ¬ (∀ {X : Type} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (H : Finset (X → Bool)) (c : X → Bool)
    (hc_meas : Measurable c) (hH_meas : ∀ h ∈ H, Measurable h)
    (m : ℕ) (δ : ℝ) (hδ : 0 < δ),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ h ∈ H, GeneralizationError D c h ≤
        EmpiricalError S c h +
          Real.sqrt ((Real.log (H.card : ℝ) + Real.log (2 / δ)) / (2 * m))}).toReal) := by
  intro HH
  have := HH (Measure.dirac true) {fun x => !x} (fun x : Bool => x) measurable_id
    (fun _ _ => measurable_from_top) 0 (1/2) (by norm_num)
  have e : {S : Fin 0 → Bool | ∀ h ∈ ({fun x => !x} : Finset (Bool → Bool)),
      GeneralizationError (Measure.dirac true) (fun x : Bool => x) h ≤
        EmpiricalError S (fun x : Bool => x) h +
          Real.sqrt ((Real.log (({fun x => !x} : Finset (Bool → Bool)).card : ℝ) + Real.log (2 / (1/2:ℝ))) / (2 * ((0:ℕ):ℝ)))} = ∅ := by
    ext S
    simp only [Finset.mem_singleton, forall_eq, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
    rw [pac_ge_not, pac_emp_zero]
    simp
  rw [e] at this
  simp at this
  norm_num at this

end FoundationsML.PAC

open FoundationsML.PAC

theorem solution : ¬ (∀ {X : Type} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (H : Finset (X → Bool)) (c : X → Bool)
    (hc_meas : Measurable c) (hH_meas : ∀ h ∈ H, Measurable h)
    (m : ℕ) (δ : ℝ) (hδ : 0 < δ),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ h ∈ H, GeneralizationError D c h ≤
        EmpiricalError S c h +
          Real.sqrt ((Real.log (H.card : ℝ) + Real.log (2 / δ)) / (2 * m))}).toReal) := FoundationsML.PAC.finite_dis
