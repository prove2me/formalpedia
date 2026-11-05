-- Prove2me | solution 1 for ClauseBound.Part.mem_map_coe_partsOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:13:36.630696+00:00
-- url     : https://prove2.me/submissions/29c3bf9f-2d4b-48f7-b955-5308e755fc92

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
import Theorems.Thm_ClauseBound_Part_mem_partsOf

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ListP
namespace ClauseBound.Part
theorem _root_.solution {E : ℕ} {τ : Multiset ℕ} : τ ∈ (partsOf E).map (fun L : List ℕ => (L : Multiset ℕ)) ↔ τ.sum = E ∧ 0 ∉ τ := by
  rw [List.mem_map]
  constructor
  · rintro ⟨L, hL, rfl⟩
    obtain ⟨hs, hp, _⟩ := mem_partsOf.1 hL
    refine ⟨by rw [Multiset.sum_coe, hs], fun h0 => ?_⟩
    have := hp 0 (Multiset.mem_coe.1 h0)
    omega
  · rintro ⟨hs, h0⟩
    refine ⟨τ.sort (· ≥ ·), mem_partsOf.2 ⟨?_, fun n hn => ?_, Multiset.pairwise_sort τ _⟩, Multiset.sort_eq τ _⟩
    · rw [← Multiset.sum_coe, Multiset.sort_eq, hs]
    · rw [Multiset.mem_sort] at hn
      exact Nat.pos_of_ne_zero fun h => h0 (h ▸ hn)
end ClauseBound.Part
