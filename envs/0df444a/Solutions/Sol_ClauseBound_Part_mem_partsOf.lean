-- Prove2me | solution 1 for ClauseBound.Part.mem_partsOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:59:10.619419+00:00
-- url     : https://prove2.me/submissions/66c99473-9ffc-4ced-99ea-6f4bd0d36666

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
import Theorems.Thm_ClauseBound_Part_mem_partsLe
import Theorems.Thm_ClauseBound_Part_ListP_le_sum_of_mem

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ListP
namespace ClauseBound.Part
theorem _root_.solution {E : ℕ} {L : List ℕ} : L ∈ partsOf E ↔ L.sum = E ∧ (∀ n ∈ L, 1 ≤ n) ∧ L.Pairwise (· ≥ ·) := by
  rw [partsOf, mem_partsLe]
  constructor
  · rintro ⟨hs, hp, hw⟩
    exact ⟨hs, fun n hn => (hp n hn).1, hw⟩
  · rintro ⟨hs, hp, hw⟩
    exact ⟨hs, fun n hn => ⟨hp n hn, hs ▸ le_sum_of_mem hn⟩, hw⟩
end ClauseBound.Part
