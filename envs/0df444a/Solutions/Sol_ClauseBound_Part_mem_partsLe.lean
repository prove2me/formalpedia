-- Prove2me | solution 1 for ClauseBound.Part.mem_partsLe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:37:49.413194+00:00
-- url     : https://prove2.me/submissions/b32c2a29-6551-41ea-8782-b8b691fc7782

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic
import Definitions.Def_PartitionStatement
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_ListP
import Theorems.Thm_ClauseBound_Part_partsLe_zero_right
import Theorems.Thm_ClauseBound_Part_partsLe_succ

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
namespace ClauseBound.Part
theorem _root_.solution (E k : ℕ) (L : List ℕ) :
    L ∈ partsLe E k ↔ L.sum = E ∧ (∀ n ∈ L, 1 ≤ n ∧ n ≤ k) ∧ L.Pairwise (· ≥ ·) := by
  induction E using Nat.strong_induction_on generalizing k L with
  | _ E ihE =>
    induction k generalizing L with
    | zero =>
      rw [partsLe_zero_right]
      constructor
      · intro h
        split_ifs at h with hE
        · rw [List.mem_singleton.1 h, hE]
          simp
        · exact absurd h List.not_mem_nil
      · rintro ⟨hs, hp, _⟩
        cases L with
        | nil =>
          rw [if_pos (by simpa using hs.symm)]
          exact List.mem_singleton.2 rfl
        | cons n L =>
          have := hp n List.mem_cons_self
          omega
    | succ k ihk =>
      rw [partsLe_succ, List.mem_append, ihk]
      constructor
      · rintro (⟨hs, hp, hw⟩ | h)
        · exact ⟨hs, fun n hn => ⟨(hp n hn).1, (hp n hn).2.trans (Nat.le_succ k)⟩, hw⟩
        · split_ifs at h with hkE
          · obtain ⟨L', hL', rfl⟩ := List.mem_map.1 h
            obtain ⟨hs, hp, hw⟩ := (ihE (E - (k + 1)) (by omega) (k + 1) L').1 hL'
            refine ⟨by rw [List.sum_cons, hs]; omega, ?_, List.pairwise_cons.2 ⟨fun n hn => (hp n hn).2, hw⟩⟩
            intro n hn
            rcases List.mem_cons.1 hn with rfl | hn
            · exact ⟨by omega, le_rfl⟩
            · exact hp n hn
          · exact absurd h List.not_mem_nil
      · rintro ⟨hs, hp, hw⟩
        cases L with
        | nil => exact Or.inl ⟨hs, fun n hn => absurd hn List.not_mem_nil, hw⟩
        | cons n L' =>
          have hn := hp n List.mem_cons_self
          obtain ⟨hw1, hw2⟩ := List.pairwise_cons.1 hw
          have hs' := hs
          rw [List.sum_cons] at hs'
          by_cases hnk : n = k + 1
          · subst hnk
            right
            rw [if_pos (by omega)]
            exact List.mem_map.2 ⟨L', (ihE _ (by omega) _ _).2 ⟨by omega, fun m hm => hp m (List.mem_cons_of_mem _ hm), hw2⟩, rfl⟩
          · left
            refine ⟨hs, ?_, hw⟩
            intro m hm
            rcases List.mem_cons.1 hm with rfl | hm
            · exact ⟨hn.1, by omega⟩
            · have h1 : n ≥ m := hw1 m hm
              exact ⟨(hp m (List.mem_cons_of_mem _ hm)).1, by omega⟩
end ClauseBound.Part
