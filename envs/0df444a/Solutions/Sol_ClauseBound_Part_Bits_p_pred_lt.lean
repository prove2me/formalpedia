-- Prove2me | solution 1 for ClauseBound.Part.Bits.p_pred_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:40:43.965065+00:00
-- url     : https://prove2.me/submissions/0db61048-a9e7-42b2-a652-3e01f970e83d

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
import Definitions.Def_ClauseBound_Part_Bits
import Theorems.Thm_ClauseBound_Part_Bits_p_one
import Theorems.Thm_ClauseBound_Part_two_le_hOf

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part ClauseBound.Part.Bits
open Finset Partitions Real
namespace ClauseBound.Part.Bits
theorem _root_.solution {lam : ℕ} (hl : 1 ≤ lam) : p (hOf lam - 1) < 2 ^ lam := by
  have h2 := two_le_hOf lam
  by_contra hn
  rcases Nat.lt_or_ge 2 (hOf lam) with h3 | h3
  · have h4 : hOf lam - 1 < hOf lam := by omega
    unfold hOf at h4 hn h3
    exact Nat.find_min _ h4 ⟨by omega, not_lt.1 hn⟩
  · rw [show hOf lam - 1 = 1 by omega, p_one] at hn
    exact hn (Nat.one_lt_two_pow (by omega))
end ClauseBound.Part.Bits
