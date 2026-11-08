-- Prove2me | solution 1 for BoundEntPPT.exists_inseparable_summand
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:15:18.490767+00:00
-- url     : https://prove2.me/submissions/66ddeb40-2573-4575-b433-d0d5432f3991

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability

open scoped Matrix ComplexOrder

namespace Aux_Q01_exists_inseparable_summand
open QAlgorithms.Entanglement

theorem sep_zero {I J : Type*} [Fintype I] [Fintype J] :
    IsSeparablePositive (0 : Matrix (I × J) (I × J) ℂ) := by
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
  · intro j; exact Fin.elim0 j
  · intro j; exact Fin.elim0 j
  · simp

theorem sep_add {I J : Type*} [Fintype I] [Fintype J] {X Y : Matrix (I × J) (I × J) ℂ}
    (hX : IsSeparablePositive X) (hY : IsSeparablePositive Y) :
    IsSeparablePositive (X + Y) := by
  obtain ⟨q1, w1, A1, B1, hw1, hd1, rfl⟩ := hX
  obtain ⟨q2, w2, A2, B2, hw2, hd2, rfl⟩ := hY
  refine ⟨q1 + q2, Fin.append w1 w2, Fin.append A1 A2, Fin.append B1 B2, ?_, ?_, ?_⟩
  · intro j
    induction j using Fin.addCases with
    | left i => simpa using hw1 i
    | right i => simpa using hw2 i
  · intro j
    induction j using Fin.addCases with
    | left i => simpa using hd1 i
    | right i => simpa using hd2 i
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

end Aux_Q01_exists_inseparable_summand

theorem solution {ι I J : Type*} [Fintype ι] [Fintype I] [Fintype J]
    (X : ι → Matrix (I × J) (I × J) ℂ)
    (h : ¬ QAlgorithms.Entanglement.IsSeparablePositive (∑ i, X i)) :
    ∃ i, ¬ QAlgorithms.Entanglement.IsSeparablePositive (X i) := by
  by_contra hall
  push_neg at hall
  apply h
  exact Finset.sum_induction _ QAlgorithms.Entanglement.IsSeparablePositive
    (fun a b ha hb => Aux_Q01_exists_inseparable_summand.sep_add ha hb)
    Aux_Q01_exists_inseparable_summand.sep_zero (fun i _ => hall i)
