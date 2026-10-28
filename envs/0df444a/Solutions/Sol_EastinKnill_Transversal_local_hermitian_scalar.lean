-- Prove2me | solution 1 for EastinKnill.Transversal.local_hermitian_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T21:06:01.134212+00:00
-- url     : https://prove2.me/submissions/1a04cf95-bd0a-44b3-a3aa-0ea339fb4f3a

import Mathlib
import Definitions.Def_EastinKnill_Transversal_Setting

open scoped Matrix
open EastinKnill.Transversal

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ j, Fintype (α j)]
    [∀ j, DecidableEq (α j)]
    (P : Matrix (∀ j, α j) (∀ j, α j) ℂ) (hP : IsCodeProjector P)
    (hdet : IsLocalErrorDetecting P) (H : ∀ j, Matrix (α j) (α j) ℂ)
    (hH : ∀ j, (H j).IsHermitian)
    (hlog : (1 - P) * (∑ j, localOp α j (H j)) * P = 0) :
    ∃ c : ℂ, (∑ j, localOp α j (H j)) * P = c • P := by
  choose c hc using fun j => hdet j (H j)
  refine ⟨∑ j, c j, ?_⟩
  have e : (∑ j, localOp α j (H j)) * P = P * (∑ j, localOp α j (H j)) * P := by
    have := hlog
    rw [sub_mul, sub_mul, one_mul] at this
    exact sub_eq_zero.mp this
  rw [e, Matrix.mul_sum, Finset.sum_mul, Finset.sum_smul]
  exact Finset.sum_congr rfl fun j _ => hc j
