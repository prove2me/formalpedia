-- Prove2me | solution 1 for ClauseBound.Part.two_pow_le_p_hOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:16:53.815815+00:00
-- url     : https://prove2.me/submissions/227dd7b4-df1e-459e-a00a-9a1bf92174e2

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

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
namespace ClauseBound.Part
theorem _root_.solution (lam : ℕ) : 2 ^ lam ≤ p (hOf lam) := by
  unfold hOf
  exact And.right (Nat.find_spec (exists_h lam))
end ClauseBound.Part
