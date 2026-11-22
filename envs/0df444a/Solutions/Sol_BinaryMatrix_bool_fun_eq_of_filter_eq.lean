-- Prove2me | solution 1 for BinaryMatrix.bool_fun_eq_of_filter_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:46:25.222283+00:00
-- url     : https://prove2.me/submissions/0c648bd2-30b3-4e23-9315-cd46555c0b7f

module
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_BinaryMatrix

set_option autoImplicit true
@[expose] public section
public section
open Finset
universe u
open BinaryMatrix
namespace BinaryMatrix
theorem _root_.solution {n : ℕ} (f g : Fin n → Bool)
    (h : Finset.univ.filter (fun j => f j = true) =
         Finset.univ.filter (fun j => g j = true)) :
    f = g := by
  funext j
  by_cases hf : f j = true <;> by_cases hg : g j = true
  · rw [hf, hg]
  · exfalso
    have : j ∈ Finset.univ.filter (fun j => f j = true) := by simp [hf]
    rw [h] at this; simp [hg] at this
  · exfalso
    have : j ∈ Finset.univ.filter (fun j => g j = true) := by simp [hg]
    rw [← h] at this; simp [hf] at this
  · simp_all
end BinaryMatrix
