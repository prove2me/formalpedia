-- Prove2me | solution 1 for DerivativeChainContinuation.mean_cost_transport_step
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T17:13:26.166995+00:00
-- url     : https://prove2.me/submissions/81b55aec-a016-4af3-811b-4dc82a028e4e

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteTransport
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_interlacing_transport_identity
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators



theorem transport_left_mass (m : ℕ) (a : Fin (m+1) → ℝ) :
    (∑ i : Fin m, ((m : ℝ)-i.val)*a i.castSucc) =
      ∑ j : Fin (m+1), ((m : ℝ)-j.val)*a j := by
  rw [Fin.sum_univ_castSucc]
  simp

theorem transport_right_mass (m : ℕ) (a : Fin (m+1) → ℝ) :
    (∑ i : Fin m, ((i.val : ℝ)+1)*a i.succ) =
      ∑ j : Fin (m+1), (j.val : ℝ)*a j := by
  rw [Fin.sum_univ_succ]
  simp

theorem transport_parent_marginal (m : ℕ) (a : Fin (m+1) → ℝ) :
    (∑ i : Fin m, (((m : ℝ)-i.val)*a i.castSucc + ((i.val : ℝ)+1)*a i.succ)) =
      (m : ℝ)*∑ j, a j := by
  rw [Finset.sum_add_distrib,transport_left_mass,transport_right_mass,←Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring






end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (m : ℕ) (hm : 0 < m)
    (a : Fin (m+1) → ℝ) (b : Fin m → ℝ)
    (A : Fin (m+1) → ℝ) (B : Fin m → ℝ)
    (hab : ∀ i, a i.castSucc ≤ b i ∧ b i ≤ a i.succ)
    (hleft : ∀ i, A i.castSucc ≤ B i+|b i-a i.castSucc|)
    (hright : ∀ i, A i.succ ≤ B i+|a i.succ-b i|) :
    (∑ j, A j)/(m+1 : ℝ) ≤ (∑ i, B i)/(m : ℝ) +
      (orderedDispersion a-orderedDispersion b)/((m : ℝ)*(m+1)) := by
  have hsum : (m : ℝ)*(∑ j, A j) ≤
      (m+1 : ℝ)*(∑ i, B i)+orderedDispersion a-orderedDispersion b := by
    rw [←transport_parent_marginal]
    have h := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin m) _ =>
      add_le_add (mul_le_mul_of_nonneg_left (hleft i) (show (0 : ℝ) ≤ (m : ℝ)-i.val from sub_nonneg.mpr (by exact_mod_cast i.isLt.le)))
        (mul_le_mul_of_nonneg_left (hright i) (show (0 : ℝ) ≤ (i.val : ℝ)+1 by positivity)))
    have hid := interlacing_transport_identity m a b hab
    simp_rw [mul_add] at h
    have hex : (∑ i : Fin m,
        (((m : ℝ)-i.val)*B i+((m : ℝ)-i.val)*|b i-a i.castSucc| +
        (((i.val : ℝ)+1)*B i+((i.val : ℝ)+1)*|a i.succ-b i|))) =
        (m+1 : ℝ)*(∑ i,B i) +
        ∑ i : Fin m, (((m : ℝ)-i.val)*|b i-a i.castSucc|+((i.val : ℝ)+1)*|a i.succ-b i|) := by
      rw [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hex,hid] at h
    linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (0 : ℝ) < m+1 := by positivity
  have hdiv := (div_le_div_iff_of_pos_right (mul_pos hmR hm1)).mpr hsum
  have hl : (∑ j, A j)/(m+1 : ℝ) =
      ((m : ℝ)*(∑ j, A j))/((m : ℝ)*(m+1)) := by field_simp
  have hr : (∑ i, B i)/(m : ℝ) +
      (orderedDispersion a-orderedDispersion b)/((m : ℝ)*(m+1)) =
      ((m+1 : ℝ)*(∑ i, B i)+orderedDispersion a-orderedDispersion b)/
        ((m : ℝ)*(m+1)) := by field_simp; ring
  rw [hl,hr]
  exact hdiv
