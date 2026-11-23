-- Prove2me | solution 1 for CompanionTheory.D.LK.koszul_differential_anticommutator
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:04.131832+00:00
-- url     : https://prove2.me/submissions/1a200b86-fe79-4e24-9d75-3841b9092280

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_KoszulDifferentialAnticommutator
import Theorems.Thm_CompanionTheory_D_LK_comm_aa
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_LK_Tri_cptk
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
theorem _root_.solution (h1 : ∀ a b i, Commute (E a b) (an i)) (h2 : ∀ a b i, Commute (E a b) (cr i))
    (haa : ∀ i j, an i * an j + an j * an i = 0) (hac : ∀ i j, an i * cr j + cr j * an i = if i = j then 1 else 0) :
    (∑ i, cc ε i • (E i.1.1 i.1.2 * an i)) * (∑ i, ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)) +
      (∑ i, ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)) * (∑ i, cc ε i • (E i.1.1 i.1.2 * an i)) =
      -∑ i, ∑ j, ∑ k, tc ε i j k • (E k.1.1 k.1.2 * (an i * an j)) := by
  simp only [Finset.mul_sum (s := univ) (f := fun i => ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)),
    Finset.sum_mul (s := univ) (f := fun i => ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)),
    ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← smul_add, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  have e : ∀ l : Pos n, cc ε l • (E l.1.1 l.1.2 * an l) * (cr k * an j * an i) +
      cr k * an j * an i * cc ε l • (E l.1.1 l.1.2 * an l) =
      if l = k then cc ε l • (E l.1.1 l.1.2 * (an j * an i)) else 0 := by
    intro l
    have c1 : cr k * an j * an i * (E l.1.1 l.1.2 * an l) = E l.1.1 l.1.2 * (cr k * an l * (an j * an i)) := by
      rw [← mul_assoc, ← (((h2 _ _ k).mul_right (h1 _ _ j)).mul_right (h1 _ _ i)).eq, mul_assoc, mul_assoc (cr k),
        mul_assoc (cr k), comm_aa an haa, mul_assoc (cr k)]
    have c2 : E l.1.1 l.1.2 * an l * (cr k * an j * an i) = E l.1.1 l.1.2 * (an l * cr k * (an j * an i)) := by
      simp only [mul_assoc]
    rw [smul_mul_assoc, mul_smul_comm, ← smul_add, c1, c2, ← mul_add, ← add_mul, hac]
    split_ifs <;> simp
  simp only [e, Finset.sum_ite_eq', mem_univ, if_true]
  rw [eq_neg_of_add_eq_zero_left (haa j i), tc]
  split_ifs with h
  · simp [cc, h.cptk]
  · simp
end CompanionTheory.D.LK
