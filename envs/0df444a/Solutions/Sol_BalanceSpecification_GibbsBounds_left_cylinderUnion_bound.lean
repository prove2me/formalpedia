-- Prove2me | solution 1 for BalanceSpecification.GibbsBounds.left_cylinderUnion_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:15:26.771192+00:00
-- url     : https://prove2.me/submissions/9abea6e9-b334-4a89-a3d4-70c84de2d5cd

module
public import Definitions.Def_BalanceSpecificaton_CylinderAlgebra
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsErgodic
public import Theorems.Thm_BalanceSpecification_real_cylinderUnion_inter
public import Theorems.Thm_BalanceSpecification_GibbsBounds_quasiBernoulli_upper
public import Theorems.Thm_BalanceSpecification_IsInvariant_cylinder_real_eq_zero
public import Theorems.Thm_BalanceSpecification_cylinder_append
public import Theorems.Thm_BalanceSpecification_cylinder_nil
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
namespace GibbsBounds
theorem _root_.solution {X : ShiftSpace A}
    {hX : X.carrier.Nonempty} {μ : ProbabilityMeasure X.carrier} {K : ℝ}
    (hB : GibbsBounds hX μ K) (hμ : IsInvariant μ)
    (S : Finset (Word A)) (l : ℕ) (hlen : ∀ a ∈ S, a.length = l)
    (k : ℤ) (v w : Word A) :
    (μ : Measure X.carrier).real
        ((⋃ a ∈ S, cylinder X a k) ∩ cylinder X (v ++ w) (k + l)) ≤
      K ^ 3 * (μ : Measure X.carrier).real
        ((⋃ a ∈ S, cylinder X a k) ∩ cylinder X v (k + l)) *
        (μ : Measure X.carrier).real (cylinder X w 0) := by
  classical
  rw [real_cylinderUnion_inter _ S l hlen _ _ (measurableSet_cylinder _ _ _),
    real_cylinderUnion_inter _ S l hlen _ _ (measurableSet_cylinder _ _ _)]
  calc
    _ ≤ ∑ a ∈ S, K ^ 3 *
        (μ : Measure X.carrier).real (cylinder X a k ∩ cylinder X v (k + l)) *
        (μ : Measure X.carrier).real (cylinder X w 0) := by
      apply Finset.sum_le_sum
      intro a ha
      have heq (z : Word A) :
          cylinder X a k ∩ cylinder X z (k + l) = cylinder X (a ++ z) k := by
        rw [cylinder_append, hlen a ha]
      rw [heq (v ++ w), heq v, ← List.append_assoc,
        hμ.cylinder_real_eq_zero (a ++ v ++ w) k,
        hμ.cylinder_real_eq_zero (a ++ v) k]
      exact hB.quasiBernoulli_upper (a ++ v) w
    _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul]
end GibbsBounds
end BalanceSpecification
