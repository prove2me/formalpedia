-- Prove2me | solution 1 for FormalCapacity.Finite.rank_blockIncidence
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-07T18:10:54.925153+00:00
-- url     : https://prove2.me/submissions/af09deca-81b0-470c-9431-9b70c7642404

import Mathlib
import Definitions.Def_capacityFinitePartitions
import Definitions.Def_capacityBlockIncidence

set_option autoImplicit false

/-!
# Finite partitions and their block-incidence rows

We use mathlib's `Finpartition` representation.  The key test partition has
one prescribed nonempty block `S` and singleton blocks outside `S`.
-/

namespace FormalCapacity.Finite

open scoped BigOperators
open Finset

variable {α R : Type*} [Fintype α] [DecidableEq α]















end FormalCapacity.Finite


/-!
# Rank of first-order block incidence

This file upgrades the row-relation characterization in `Partition.lean` to
the finite-dimensional rank formula `2^n - n`.
-/

namespace FormalCapacity.Finite

open scoped BigOperators
open Finset Module

variable {α : Type*} [Fintype α] [DecidableEq α]



























theorem card_nonemptyBlock :
    Fintype.card (NonemptyBlock α) = 2 ^ Fintype.card α - 1 := by
  rw [Fintype.card_congr (nonemptyBlockEquivNeEmpty (α := α))]
  simpa using Fintype.card_subtype_compl (fun B : Finset α ↦ B = ∅)

theorem labelSum_ne_zero [Nonempty α] : labelSum (α := α) ≠ 0 := by
  obtain ⟨i⟩ := (inferInstance : Nonempty α)
  intro h
  have hfun := LinearMap.congr_fun h (fun j ↦ if j = i then (1 : ℚ) else 0)
  simp [labelSum] at hfun

/-- The row-nullspace has dimension `n - 1`. -/
theorem finrank_ker_blockIncidenceTranspose [Nonempty α] :
    finrank ℚ (blockIncidenceTranspose (α := α)).ker = Fintype.card α - 1 := by
  rw [← (incidenceKernelEquivZeroSum (α := α)).finrank_eq]
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero
    (labelSum_ne_zero (α := α))
  rw [Module.finrank_pi] at h
  omega







end FormalCapacity.Finite


/-!
# Rank of first-order block incidence

This file upgrades the row-relation characterization in `Partition.lean` to
the finite-dimensional rank formula `2^n - n`.
-/

open FormalCapacity.Finite

open scoped BigOperators
open Finset Module

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem solution [Nonempty α] :
    finrank ℚ (blockIncidenceTranspose (α := α)).range =
      2 ^ Fintype.card α - Fintype.card α := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (blockIncidenceTranspose (α := α))
  rw [finrank_ker_blockIncidenceTranspose, Module.finrank_pi,
    card_nonemptyBlock] at h
  have hn : 1 ≤ Fintype.card α := Fintype.card_pos_iff.mpr inferInstance
  have hp : 1 ≤ 2 ^ Fintype.card α := Nat.one_le_two_pow
  have hadd :
      finrank ℚ (blockIncidenceTranspose (α := α)).range + Fintype.card α =
        2 ^ Fintype.card α := by
    omega
  calc
    finrank ℚ (blockIncidenceTranspose (α := α)).range =
        (finrank ℚ (blockIncidenceTranspose (α := α)).range +
          Fintype.card α) - Fintype.card α :=
      (Nat.add_sub_cancel_right _ _).symm
    _ = 2 ^ Fintype.card α - Fintype.card α := congrArg (fun n ↦ n - Fintype.card α) hadd
