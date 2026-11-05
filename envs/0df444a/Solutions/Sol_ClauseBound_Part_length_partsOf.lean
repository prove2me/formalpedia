-- Prove2me | solution 1 for ClauseBound.Part.length_partsOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:44:48.144861+00:00
-- url     : https://prove2.me/submissions/114d0897-0a2c-4f7e-bf3a-60780b9e08ca

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
import Theorems.Thm_ClauseBound_Part_mem_map_coe_partsOf
import Theorems.Thm_ClauseBound_Part_nodup_map_coe_partsOf

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ListP
namespace ClauseBound.Part
theorem _root_.solution (E : ℕ) : (partsOf E).length = Partitions.p E := by
  have h1 : ((partsOf E).map fun L : List ℕ => (L : Multiset ℕ)).toFinset = (univ : Finset (Nat.Partition E)).image fun q => q.parts := by
    ext τ
    rw [List.mem_toFinset, mem_map_coe_partsOf, Finset.mem_image]
    constructor
    · rintro ⟨hs, h0⟩
      exact ⟨⟨τ, fun {i} hi => Nat.pos_of_ne_zero fun h => h0 (h ▸ hi), hs⟩, Finset.mem_univ _, rfl⟩
    · rintro ⟨q, _, rfl⟩
      exact ⟨q.parts_sum, fun h0 => absurd (q.parts_pos h0) (lt_irrefl 0)⟩
  have h2 := List.toFinset_card_of_nodup (nodup_map_coe_partsOf E)
  rw [h1, Finset.card_image_of_injective _ fun q q' h => Nat.Partition.ext h, Finset.card_univ, List.length_map] at h2
  exact h2.symm
end ClauseBound.Part
