-- Prove2me | solution 1 for BooleanFun.pow_eq_self_imp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:00:19.569782+00:00
-- url     : https://prove2.me/submissions/67934e32-b575-4f13-8304-dc74084094ec

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_BooleanFun_Auxiliary

set_option autoImplicit false
open BooleanFun
open Finset Pi
variable {α : Type*} {β : Type*}
variable {s : Finset α}
variable {ι : Type*} [Fintype ι]
variable {κ : Type*}
variable {R : Type*} {M : Type*}
variable [Ring R] [AddCommGroup M] [Module R M]
namespace BooleanFun
theorem _root_.solution {ρ : ℝ} {k : ℕ}:
    ρ ^ k = ρ → (k = 1 ∨ ρ = 0 ∨ ρ = 1 ∨ ρ = -1) := by
  intro h
  cases k with
  | zero => right; right; left; symm; rwa [pow_zero] at h
  | succ k =>
    by_cases hρ : ρ = 0
    · right; left; assumption
    · rw [pow_succ] at h
      nth_rewrite 3 [← one_mul ρ] at h
      have h := mul_right_cancel₀ hρ h
      obtain h'|h'|⟨h', _⟩ := pow_eq_one_iff_cases.mp h
      · left; simp [h']
      · right; right; left; assumption
      · right; right; right; assumption
end BooleanFun
