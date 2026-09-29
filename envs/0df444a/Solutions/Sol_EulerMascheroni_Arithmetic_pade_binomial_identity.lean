-- Prove2me | solution 1 for EulerMascheroni.Arithmetic.pade_binomial_identity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T14:17:20.578973+00:00
-- url     : https://prove2.me/submissions/cf00a731-777a-46e4-ac75-ffafbed50fad

import Definitions.Def_eulerMascheroni_padeTransform
import Theorems.Thm_EulerMascheroni_Arithmetic_binomial_transform_recurrence
import Theorems.Thm_EulerMascheroni_Arithmetic_quotient_coefficient_properties
set_option autoImplicit false
open EulerMascheroni.Arithmetic

namespace EulerPadeConnection

lemma transform_initial (a : ℝ) :
    binomialTransform (quotientCoeff a) 0 = a ∧
    binomialTransform (quotientCoeff a) 1 = 2*a-1 := by
  constructor
  · simp [binomialTransform, quotientCoeff]
  · simp [binomialTransform, quotientCoeff, Finset.sum_range_succ, Nat.factorial]
    ring

lemma pade_identity (a : ℝ) (n : ℕ) :
    (padeQ n : ℝ)*a - (padeP n : ℝ) =
      (n.factorial:ℝ)^2 * binomialTransform (quotientCoeff a) n := by
  have hf := fun k => ((quotient_coefficient_properties a).2 k).1
  have ht := binomial_transform_recurrence (quotientCoeff a) hf
  have hinit := transform_initial a
  induction n using Nat.twoStepInduction with
  | zero => simpa [padeP, padeQ, padeSeq] using hinit.1.symm
  | one => simpa [padeP, padeQ, padeSeq] using hinit.2.symm
  | more n ih ih' =>
    have hh := ht n
    change ((padeSeq 1 2 (n+2) : ℤ) : ℝ)*a - ((padeSeq 0 1 (n+2) : ℤ) : ℝ) = _
    rw [padeSeq, padeSeq]
    push_cast
    change _ = _ at ih ih'
    simp only [padeQ, padeP] at ih ih'
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at ih' ⊢
    linear_combination (2*(n:ℝ)+4)*ih' - ((n:ℝ)+1)^2*ih -
      ((n:ℝ)+1)^2*(n.factorial:ℝ)^2*hh


end EulerPadeConnection


theorem solution (a : ℝ) (n : ℕ) :
    (padeQ n : ℝ)*a - (padeP n : ℝ) =
      (n.factorial:ℝ)^2 * binomialTransform (quotientCoeff a) n := by
  exact EulerPadeConnection.pade_identity a n

#print axioms solution
