-- Prove2me | solution 1 for BalanceSpecification.gibbs_suffix_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:15:27.546792+00:00
-- url     : https://prove2.me/submissions/c2e2ce88-555d-48e1-879f-08c430fc4159

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsErgodic
public import Theorems.Thm_BalanceSpecification_GibbsBounds_quasiBernoulli_upper
public import Theorems.Thm_BalanceSpecification_IsInvariant_cylinder_real_eq_zero
public import Theorems.Thm_BalanceSpecification_cylinder_append
public import Theorems.Thm_BalanceSpecification_cylinder_nil
public import Theorems.Thm_BalanceSpecification_disjoint_cylinder
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_measurableSet_cylinder
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.cylinder_nil
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage



set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Set
open scoped symmDiff ENNReal
open BalanceSpecification
variable {A : Type*} [TopologicalSpace A] [Fintype A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A]
namespace BalanceSpecification
theorem _root_.solution {X : ShiftSpace A} {hX : X.carrier.Nonempty}
    {μ : ProbabilityMeasure X.carrier} (hμ : IsInvariant μ) {K : ℝ}
    (hG : GibbsBounds hX μ K) (S : Finset (Word A)) {l : ℕ}
    (hS : ∀ a ∈ S, a.length = l) (k : ℤ) (v w : Word A) :
    (μ : Measure X.carrier).real
        (cylinder X (v ++ w) k ∩
          (⋃ a ∈ S, cylinder X a (k + (v ++ w).length))) ≤
      K ^ 3 * (μ : Measure X.carrier).real (cylinder X v 0) *
        (μ : Measure X.carrier).real
          (cylinder X w (k + v.length) ∩
            (⋃ a ∈ S, cylinder X a (k + (v ++ w).length))) := by
  classical
  let ρ : Measure X.carrier := μ
  have hd (C : Set X.carrier) :
      Set.PairwiseDisjoint (S : Set (Word A))
        (fun a => C ∩ cylinder X a (k + (v ++ w).length)) := by
    intro a ha b hb hab
    exact (disjoint_cylinder X ((hS a ha).trans (hS b hb).symm) hab _).mono
      Set.inter_subset_right Set.inter_subset_right
  have hsum (C : Set X.carrier) (hC : MeasurableSet C) :
      ρ.real (C ∩ (⋃ a ∈ S, cylinder X a (k + (v ++ w).length))) =
        ∑ a ∈ S, ρ.real (C ∩ cylinder X a (k + (v ++ w).length)) := by
    simp_rw [Set.inter_iUnion]
    exact measureReal_biUnion_finset (hd C)
      (fun a _ => hC.inter (measurableSet_cylinder X a _))
  rw [hsum _ (measurableSet_cylinder X (v ++ w) k),
    hsum _ (measurableSet_cylinder X w (k + v.length)), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have hleft : cylinder X (v ++ w) k ∩ cylinder X a (k + (v ++ w).length) =
      cylinder X (v ++ (w ++ a)) k := by
    rw [← cylinder_append, List.append_assoc]
  have hright : cylinder X w (k + v.length) ∩ cylinder X a (k + (v ++ w).length) =
      cylinder X (w ++ a) (k + v.length) := by
    rw [cylinder_append]
    simp only [List.length_append, Nat.cast_add, add_assoc]
  rw [hleft, hright]
  change (μ : Measure X.carrier).real (cylinder X (v ++ (w ++ a)) k) ≤ _
  rw [hμ.cylinder_real_eq_zero, hμ.cylinder_real_eq_zero (w ++ a) (k + v.length)]
  exact hG.quasiBernoulli_upper v (w ++ a)
end BalanceSpecification
