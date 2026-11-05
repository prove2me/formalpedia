-- Prove2me | solution 1 for ClausesOccur.expHalf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:07:55.792128+00:00
-- url     : https://prove2.me/submissions/01540b9c-923e-428b-bf53-ca289b0c06d3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClausesOccurStatement
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Rename_Time
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OccurM_Arith

set_option autoImplicit false
section
section
open ClausesOccur
open MainTheoremForms
namespace ClausesOccur
theorem _root_.solution : ExpHalfStmt := by
  intro k m
  unfold expClauses expM
  rw [Real.sqrt_eq_rpow]
end ClausesOccur
