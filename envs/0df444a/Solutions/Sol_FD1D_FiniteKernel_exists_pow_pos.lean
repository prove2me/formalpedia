-- Prove2me | solution 1 for FD1D.FiniteKernel.exists_pow_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:42:32.899796+00:00
-- url     : https://prove2.me/submissions/5b2cec80-bdf5-4e8d-8032-97b60981bab4

import Definitions.Def_FD1D_Expectations
import Definitions.Def_FD1D_FiniteConvergence
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteKernel_pow_nonneg
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.DeletionRule.kernel_apply
attribute [local simp] FD1D.FiniteLaw.expect_const


section
namespace FD1D
noncomputable section
open Filter
open scoped BigOperators Topology
namespace FiniteKernel
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
private theorem reachTime_spec
    (K : FiniteKernel α) (hirr : K.Irreducible) (x y : α) :
    0 < K.pow (reachTime K hirr x y) x y :=
  Classical.choose_spec (hirr x y)
private theorem pow_loop_pos
    (K : FiniteKernel α) (hloop : K.HasPositiveLoops)
    (x : α) (n : ℕ) :
    0 < K.pow n x x := by
  induction n with
  | zero =>
      simp [FiniteKernel.pow_zero]
  | succ n ih =>
      rw [show n + 1 = n + 1 by rfl, K.pow_add]
      have hterm : 0 < K.pow n x x * K.pow 1 x x := by
        simpa using mul_pos ih (hloop x)
      exact lt_of_lt_of_le hterm
        (Finset.single_le_sum
          (fun y _ =>
            mul_nonneg (K.pow_nonneg n x y) (K.pow_nonneg 1 y x))
          (Finset.mem_univ x))
end FiniteKernel
end
end FD1D
end

set_option autoImplicit true
open FD1D
noncomputable section
open Filter
open scoped BigOperators Topology
open FD1D.FiniteKernel
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
namespace FD1D.FiniteKernel
theorem _root_.solution
    (K : FiniteKernel α) (hirr : K.Irreducible)
    (hloop : K.HasPositiveLoops) :
    ∃ N : ℕ, 0 < N ∧ ∀ x y, 0 < K.pow N x y := by
  let N : ℕ := 1 + ∑ x, ∑ y, reachTime K hirr x y
  refine ⟨N, by simp [N], ?_⟩
  intro x y
  let n := reachTime K hirr x y
  have hnInner : n ≤ ∑ z, reachTime K hirr x z := by
    exact Finset.single_le_sum
      (fun z _ => Nat.zero_le (reachTime K hirr x z))
      (Finset.mem_univ y)
  have hnSum :
      (∑ z, reachTime K hirr x z) ≤
        ∑ w, ∑ z, reachTime K hirr w z := by
    exact Finset.single_le_sum
      (fun w _ => Nat.zero_le (∑ z, reachTime K hirr w z))
      (Finset.mem_univ x)
  have hnN : n ≤ N := by
    dsimp [N]
    omega
  have hsplit : n + (N - n) = N := Nat.add_sub_of_le hnN
  rw [← hsplit, K.pow_add]
  exact lt_of_lt_of_le
    (mul_pos (reachTime_spec K hirr x y)
      (pow_loop_pos K hloop y (N - n)))
    (Finset.single_le_sum
      (fun z _ =>
        mul_nonneg (K.pow_nonneg n x z) (K.pow_nonneg (N - n) z y))
      (Finset.mem_univ y))
end FD1D.FiniteKernel
