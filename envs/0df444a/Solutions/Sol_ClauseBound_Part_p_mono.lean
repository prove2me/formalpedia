-- Prove2me | solution 1 for ClauseBound.Part.p_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:14:31.711187+00:00
-- url     : https://prove2.me/submissions/1f1586a3-edea-4c8f-b152-ff8e9b74dc1a

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
import Theorems.Thm_ClauseBound_Part_card_count_ge

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
namespace ClauseBound.Part
theorem _root_.solution {E E' : ℕ} (h : E ≤ E') : p E ≤ p E' := by
  have h1 := card_count_ge (E := E') (v := 1) (k := E' - E) le_rfl (by omega)
  rw [show E' - (E' - E) * 1 = E by omega] at h1
  rw [← h1, p, ← card_univ]
  exact card_le_card (filter_subset _ _)
end ClauseBound.Part
