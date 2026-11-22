-- Prove2me | solution 1 for BinaryMatrix.shatters_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:41:44.96949+00:00
-- url     : https://prove2.me/submissions/4fc48958-2c84-4d02-849b-6f1b63af7550

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
theorem _root_.solution {m n : ℕ} (M : BinaryMatrix m n) (S : Finset (Fin n)) :
    M.shatters S ↔ M.toFinsetFamily.Shatters S := by
  constructor
  · -- Forward: our definition → Mathlib's
    intro hM t ht
    obtain ⟨i, hi⟩ := hM t ht
    refine ⟨Finset.univ.filter (fun j => M i j = true), ?_, ?_⟩
    · simp only [toFinsetFamily, mem_image, mem_univ, true_and]
      exact ⟨i, rfl⟩
    · ext j
      simp only [mem_inter, mem_filter, mem_univ, true_and]
      constructor
      · simp_all
      · intro hjt
        have hjS := ht hjt
        exact ⟨hjS, (hi j hjS).mpr hjt⟩
  · -- Backward: Mathlib's → our definition
    intro hS t ht
    obtain ⟨u, hu, hut⟩ := hS ht
    simp only [toFinsetFamily, mem_image, mem_univ, true_and] at hu
    obtain ⟨i, rfl⟩ := hu
    refine ⟨i, fun j hj => ?_⟩
    constructor
    · intro hMij
      have : j ∈ S ∩ Finset.univ.filter (fun j => M i j = true) := by
        simp only [mem_inter, mem_filter, mem_univ, true_and]; exact ⟨hj, hMij⟩
      rwa [hut] at this
    · intro hjt
      have : j ∈ S ∩ Finset.univ.filter (fun j => M i j = true) := by rw [hut]; exact hjt
      simp only [mem_inter, mem_filter, mem_univ, true_and] at this
      exact this.2
end BinaryMatrix
