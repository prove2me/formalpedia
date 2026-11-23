-- Prove2me | solution 1 for CompanionTheory.D.LK.beta_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:41.800801+00:00
-- url     : https://prove2.me/submissions/7e9c6313-71c9-4aa3-b262-309e36c6306f

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_KoszulDifferentialAnticommutator
import Theorems.Thm_CompanionTheory_D_LK_tc_assoc
import Theorems.Thm_CompanionTheory_D_LK_self_neg
import Theorems.Thm_CompanionTheory_D_LK_comm_aa
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
theorem _root_.solution (haa : ∀ i j, an i * an j + an j * an i = 0) (hcc : ∀ i j, cr i * cr j + cr j * cr i = 0)
    (hac : ∀ i j, an i * cr j + cr j * an i = if i = j then 1 else 0) :
    (∑ i, ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)) * (∑ i, ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)) = 0 := by
  let t : Pos n × Pos n × Pos n → ℂ := fun p => tc ε p.1 p.2.1 p.2.2
  have e : (∑ i, ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)) =
      ∑ p : Pos n × Pos n × Pos n, t p • (cr p.2.2 * an p.2.1 * an p.1) := by
    simp only [Fintype.sum_prod_type, t]
  have ex : ∀ i j k i' j' k' : Pos n, cr k * an j * an i * (cr k' * an j' * an i') =
      (if i = k' then cr k * (an j * (an j' * an i')) else 0) - (if j = k' then cr k * (an j' * an i' * an i) else 0) +
        cr k * cr k' * ((an j * an i) * (an j' * an i')) := by
    intro i j k i' j' k'
    have a1 := eq_sub_of_add_eq (hac i k')
    have a2 := eq_sub_of_add_eq (hac j k')
    calc _ = cr k * (an j * (an i * cr k')) * (an j' * an i') := by simp only [mul_assoc]
      _ = cr k * (an j * (if i = k' then 1 else 0) - (an j * cr k') * an i) * (an j' * an i') := by
          rw [a1, mul_sub, mul_assoc (an j)]
      _ = _ := by
          rw [a2, comm_aa an haa i i' j']
          split_ifs <;> noncomm_ring
  rw [e, Finset.sum_mul_sum]
  simp only [smul_mul_smul_comm, ex, smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h3 : ∑ p : Pos n × Pos n × Pos n, ∑ q : Pos n × Pos n × Pos n,
      (t p * t q) • (cr p.2.2 * cr q.2.2 * ((an p.2.1 * an p.1) * (an q.2.1 * an q.1))) = 0 := by
    apply self_neg
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [mul_comm (t q), eq_neg_of_add_eq_zero_left (hcc q.2.2 p.2.2), neg_mul, smul_neg, ← mul_assoc (an q.2.1 * an q.1),
      comm_aa an haa, mul_assoc (an p.2.1), comm_aa an haa, ← mul_assoc (an p.2.1)]
  rw [h3, add_zero, sub_eq_zero]
  have L : ∑ p : Pos n × Pos n × Pos n, ∑ q : Pos n × Pos n × Pos n,
      (t p * t q) • (if p.1 = q.2.2 then cr p.2.2 * (an p.2.1 * (an q.2.1 * an q.1)) else 0) =
      ∑ p, ∑ q, ∑ r, ∑ k, (∑ i, tc ε p q i * tc ε i r k) • (cr k * (an r * an q * an p)) := by
    simp only [Fintype.sum_prod_type, t, smul_ite, smul_zero, Finset.sum_ite_eq, mem_univ, if_true, Finset.sum_smul]
    symm
    calc _ = ∑ p, ∑ q, ∑ i, ∑ r, ∑ k, (tc ε p q i * tc ε i r k) • (cr k * (an r * an q * an p)) := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
          exact (Finset.sum_congr rfl fun r _ => Finset.sum_comm).trans Finset.sum_comm
      _ = ∑ x : Pos n × Pos n, ∑ y : Pos n × Pos n × Pos n,
            (tc ε x.1 x.2 y.1 * tc ε y.1 y.2.1 y.2.2) • (cr y.2.2 * (an y.2.1 * an x.2 * an x.1)) := by
          simp only [Fintype.sum_prod_type]
      _ = _ := by
          rw [Finset.sum_comm]
          simp only [Fintype.sum_prod_type, mul_comm (tc ε _ _ _) (tc ε _ _ _), mul_assoc]
  have R' : ∑ p : Pos n × Pos n × Pos n, ∑ q : Pos n × Pos n × Pos n,
      (t p * t q) • (if p.2.1 = q.2.2 then cr p.2.2 * (an q.2.1 * an q.1 * an p.1) else 0) =
      ∑ p, ∑ q, ∑ r, ∑ k, (∑ j, tc ε q r j * tc ε p j k) • (cr k * (an r * an q * an p)) := by
    simp only [Fintype.sum_prod_type, t, smul_ite, smul_zero, Finset.sum_ite_eq, mem_univ, if_true, Finset.sum_smul]
    refine Finset.sum_congr rfl fun p _ => ?_
    calc _ = ∑ x : Pos n × Pos n, ∑ y : Pos n × Pos n,
            (tc ε p x.1 x.2 * tc ε y.1 y.2 x.1) • (cr x.2 * (an y.2 * an y.1 * an p)) := by
          simp only [Fintype.sum_prod_type]
      _ = _ := by
          rw [Finset.sum_comm]
          simp only [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_comm]
          simp only [mul_comm (tc ε p _ _)]
  rw [L, R']
  simp only [tc_assoc]
end CompanionTheory.D.LK
