-- Prove2me | solution 1 for ClauseBound.Part.p_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:46:56.966805+00:00
-- url     : https://prove2.me/submissions/6c72591c-3286-4241-b21a-4f8275aecf97

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
import Theorems.Thm_ClauseBound_Part_ListP_length_partsLe_aux
import Theorems.Thm_ClauseBound_Part_length_partsOf

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ListP
namespace ClauseBound.Part
theorem _root_.solution (E : ℕ) : Partitions.p E ≤ 2 ^ E := by
  rw [← length_partsOf]
  exact (length_partsLe_aux E E).1
end ClauseBound.Part
