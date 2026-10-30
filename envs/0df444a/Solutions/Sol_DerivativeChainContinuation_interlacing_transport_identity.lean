-- Prove2me | solution 1 for DerivativeChainContinuation.interlacing_transport_identity
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T17:11:23.979991+00:00
-- url     : https://prove2.me/submissions/676235b6-7335-4d4c-8c29-3f02c8b75865

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteTransport
import Definitions.Def_DerivativeChainPrivate_foundations
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








end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (m : ℕ) (a : Fin (m+1) → ℝ) (b : Fin m → ℝ)
    (hab : ∀ i, a i.castSucc ≤ b i ∧ b i ≤ a i.succ) :
    (∑ i : Fin m, (((m : ℝ)-i.val)*|b i-a i.castSucc| +
      ((i.val : ℝ)+1)*|a i.succ-b i|)) = orderedDispersion a-orderedDispersion b := by
  have habs : ∀ i : Fin m, |b i-a i.castSucc|=b i-a i.castSucc ∧
      |a i.succ-b i|=a i.succ-b i := by
    intro i
    exact ⟨abs_of_nonneg (sub_nonneg.mpr (hab i).1),abs_of_nonneg (sub_nonneg.mpr (hab i).2)⟩
  simp_rw [(habs _).1,(habs _).2,mul_sub]
  have he (i : Fin m) :
      ((m : ℝ)-i.val)*b i-((m : ℝ)-i.val)*a i.castSucc +
        (((i.val : ℝ)+1)*a i.succ-((i.val : ℝ)+1)*b i) =
      ((i.val : ℝ)+1)*a i.succ-((m : ℝ)-i.val)*a i.castSucc-
        (2*(i.val : ℝ)+1-m)*b i := by ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,transport_right_mass,transport_left_mass,
    ←Finset.sum_sub_distrib]
  unfold orderedDispersion
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring
