-- Prove2me | solution 1 for BalanceSpecification.sum_follower_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:14:28.723842+00:00
-- url     : https://prove2.me/submissions/0050b421-999b-4bdd-bdff-533955c53f99

module
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsBalance
public import Theorems.Thm_BalanceSpecification_cylinder_eq_empty_of_not_mem_language


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution (μ : ProbabilityMeasure X.carrier) (u : Word A) (n : ℕ) :
    (∑ w ∈ followerFinset (language X) u n,
      (μ : Measure X.carrier).real (cylinder X (u ++ w) 0)) =
        (μ : Measure X.carrier).real (cylinder X u 0) := by
  classical
  calc
    _ = ∑ w ∈ wordFinset (language X) n,
        (μ : Measure X.carrier).real (cylinder X (u ++ w) 0) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro w hw hnot
      have hforbid : u ++ w ∉ language X := by
        intro h
        exact hnot (Finset.mem_filter.mpr ⟨hw, h⟩)
      rw [cylinder_eq_empty_of_not_mem_language X hforbid, measureReal_empty]
    _ = _ := sum_cylinder_append_right μ u n 0
end BalanceSpecification
