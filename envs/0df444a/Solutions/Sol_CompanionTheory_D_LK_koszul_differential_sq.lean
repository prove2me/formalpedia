-- Prove2me | solution 1 for CompanionTheory.D.LK.koszul_differential_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:47.801331+00:00
-- url     : https://prove2.me/submissions/f9754982-50f4-4664-bdbf-37cb5a62cea9

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_KoszulDifferentialAnticommutator
import Theorems.Thm_CompanionTheory_D_LK_sum_tc
import Theorems.Thm_CompanionTheory_D_LK_self_neg
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car Formalism.REAL
open CompanionTheory.D.DSIC (KRel)
variable {n : ℕ} {ε : Fin n → Bool}
variable {R : Type} [Ring R] [Algebra ℂ R] (E : Fin n → Fin n → R) (an cr : Pos n → R)
namespace CompanionTheory.D.LK
theorem _root_.solution (hE : KRel ε E) (h1 : ∀ a b i, Commute (E a b) (an i)) (haa : ∀ i j, an i * an j + an j * an i = 0) :
    (∑ i, cc ε i • (E i.1.1 i.1.2 * an i)) * (∑ i, cc ε i • (E i.1.1 i.1.2 * an i)) =
      ∑ i, ∑ j, ∑ k, tc ε i j k • (E k.1.1 k.1.2 * (an i * an j)) := by
  set T : Pos n → Pos n → R := fun i j => ∑ k, tc ε i j k • (E k.1.1 k.1.2 * (an i * an j)) with hT
  set U : Pos n → Pos n → R := fun i j => (cc ε i * cc ε j) • (E i.1.1 i.1.2 * E j.1.1 j.1.2 * (an i * an j)) with hU
  have e : (∑ i, cc ε i • (E i.1.1 i.1.2 * an i)) * (∑ i, cc ε i • (E i.1.1 i.1.2 * an i)) = ∑ i, ∑ j, U i j := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, hU, mul_assoc, ← mul_assoc (an i), ← (h1 _ _ i).eq]
    simp only [mul_assoc]
  have key : ∀ i j, U i j + U j i = T i j + T j i := by
    intro i j
    have ha : an j * an i = -(an i * an j) := eq_neg_of_add_eq_zero_right (haa i j)
    simp only [hT, hU, sum_tc (f := fun k => E k.1.1 k.1.2 * (an i * an j)),
      sum_tc (f := fun k => E k.1.1 k.1.2 * (an j * an i))]
    rw [ha]
    by_cases ci : cpt ε i
    swap
    · simp [cc, ci]
    by_cases cj : cpt ε j
    swap
    · simp [cc, cj]
    have := hE i.1.1 i.1.2 j.1.1 j.1.2 ci cj
    simp only [cc, eq_true ci, eq_true cj, if_true, true_and, mul_one, one_smul, mul_neg, ← sub_eq_add_neg, ← sub_mul, this]
    split_ifs <;> simp [sub_mul, sub_eq_add_neg, add_mul]
  rw [e, ← sub_eq_zero]
  apply self_neg
  rw [eq_neg_iff_add_eq_zero]
  have s1 : ∑ i, ∑ j, U i j = ∑ i, ∑ j, U j i := Finset.sum_comm
  have s2 : ∑ i, ∑ j, T i j = ∑ i, ∑ j, T j i := Finset.sum_comm
  have s3 : ∑ i, ∑ j, U i j + ∑ i, ∑ j, U j i = ∑ i, ∑ j, T i j + ∑ i, ∑ j, T j i := by
    simp only [← Finset.sum_add_distrib, key]
  rw [← s1, ← s2] at s3
  change (∑ i, ∑ j, U i j - ∑ i, ∑ j, T i j) + (∑ i, ∑ j, U i j - ∑ i, ∑ j, T i j) = 0
  rw [sub_add_sub_comm, s3, sub_self]
end CompanionTheory.D.LK
