-- Prove2me | solution 1 for DeletionCode.WitnessAlgebra.signed_sum_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:49.201104+00:00
-- url     : https://prove2.me/submissions/3f8a9304-9744-4eb5-8be4-359a190de6bf

import Definitions.Def_DeletionCode_GeneratingBlocks
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Definitions.Def_DeletionCode_WitnessAlgebra

set_option autoImplicit true
open DeletionCode DeletionCode.WitnessAlgebra
open scoped BigOperators
namespace DeletionCode.WitnessAlgebra
theorem _root_.solution {I J V : Type*} [Fintype I] [Fintype J]
    [AddCommGroup V] [Module ℚ V] (G : I → V) (hG : LinearIndependent ℚ G)
    (label : J → I) (positive : J → Prop) [DecidablePred positive]
    (hsum : (∑ j, (if positive j then (1 : ℚ) else -1) • G (label j)) = 0) :
    Even (Fintype.card J) := by
  classical
  let a : J → ℚ := fun j => if positive j then 1 else -1
  let c : I → ℚ := fun i => ∑ j, if label j = i then a j else 0
  have hsumsmul (s : Finset J) (f : J → ℚ) (v : V) :
      (∑ j ∈ s, f j) • v = ∑ j ∈ s, f j • v := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih => simp [hj, add_smul, ih]
  have hgrouped : ∑ i, c i • G i = 0 := by
    calc
      ∑ i, c i • G i = ∑ j, ∑ i, (if label j = i then a j else 0) • G i := by
        simp only [c, hsumsmul]
        rw [Finset.sum_comm]
      _ = ∑ j, a j • G (label j) := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [ite_smul, zero_smul]
        simp
      _ = 0 := hsum
  have hc : ∀ i, c i = 0 := fun i =>
    (linearIndependent_iff'.mp hG) Finset.univ c hgrouped i (Finset.mem_univ i)
  have htotal : ∑ j, a j = 0 := by
    calc
      ∑ j, a j = ∑ i, c i := by
        simp only [c]
        rw [Finset.sum_comm]
        simp
      _ = 0 := Finset.sum_eq_zero (fun i _ => hc i)
  have hcounts : ((Finset.univ.filter positive).card : ℚ) =
      ((Finset.univ.filter (fun j => ¬positive j)).card : ℚ) := by
    have hdiff := htotal
    simp only [a, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one,
      mul_neg, mul_one] at hdiff
    linarith
  have hnat : (Finset.univ.filter positive).card =
      (Finset.univ.filter (fun j => ¬positive j)).card := by exact_mod_cast hcounts
  have hpartition := Finset.card_filter_add_card_filter_not (s := Finset.univ) positive
  refine ⟨(Finset.univ.filter positive).card, ?_⟩
  simpa only [hnat, Finset.card_univ] using hpartition.symm
end DeletionCode.WitnessAlgebra
