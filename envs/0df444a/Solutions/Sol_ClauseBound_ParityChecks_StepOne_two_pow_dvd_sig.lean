-- Prove2me | solution 1 for ClauseBound.ParityChecks.StepOne.two_pow_dvd_sig
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:08:19.468018+00:00
-- url     : https://prove2.me/submissions/456e3390-4e22-4404-85ca-ae6f96b9e77a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_ParityChecks_StepOne

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.StepOne
open Finset _root_.ParityChecks
variable {E : Type} {r : ℕ}
namespace ClauseBound.ParityChecks.StepOne
theorem _root_.solution (i : ℕ) : (2 : ℤ) ^ (i - 1) ∣ sig i := by
  unfold sig
  split_ifs with h
  · rw [h]; exact one_dvd _
  · exact Dvd.intro_left _ rfl
end ClauseBound.ParityChecks.StepOne
