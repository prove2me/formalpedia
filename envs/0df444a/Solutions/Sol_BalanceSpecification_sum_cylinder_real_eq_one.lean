-- Prove2me | solution 1 for BalanceSpecification.sum_cylinder_real_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:20:16.974786+00:00
-- url     : https://prove2.me/submissions/bb7d49b5-78f1-465f-9603-9877274b64db

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Measures
public import Theorems.Thm_BalanceSpecification_disjoint_cylinder
public import Theorems.Thm_BalanceSpecification_measurableSet_cylinder
public import Theorems.Thm_BalanceSpecification_iUnion_cylinder_wordFinset
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
attribute [local simp] BalanceSpecification.mem_wordFinset



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A]
variable [Fintype A] [DiscreteTopology A] [MeasurableSpace A] [BorelSpace A]
namespace BalanceSpecification
theorem _root_.solution (X : ShiftSpace A) (μ : ProbabilityMeasure X.carrier)
    (n : ℕ) (k : ℤ) :
    (∑ w ∈ wordFinset (language X) n,
      (μ : Measure X.carrier).real (cylinder X w k)) = 1 := by
  have hd : Set.PairwiseDisjoint (wordFinset (language X) n : Set (Word A))
      (fun w => cylinder X w k) := by
    intro v hv w hw hvw
    apply disjoint_cylinder X _ hvw k
    exact (mem_wordFinset.mp hv).2.trans (mem_wordFinset.mp hw).2.symm
  rw [← measureReal_biUnion_finset hd (fun w _ => measurableSet_cylinder X w k),
    iUnion_cylinder_wordFinset, probReal_univ]
end BalanceSpecification
