-- Prove2me | solution 1 for ClauseBound.Part.partsLe_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:36:44.189422+00:00
-- url     : https://prove2.me/submissions/b74a0281-db2c-48a0-8b26-ebd6338ad096

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

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
namespace ClauseBound.Part
theorem _root_.solution (E : ℕ) : partsLe E 0 = if E = 0 then [[]] else [] := by
  cases E <;> rw [partsLe] <;> simp
end ClauseBound.Part
