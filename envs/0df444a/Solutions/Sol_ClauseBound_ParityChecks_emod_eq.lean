-- Prove2me | solution 1 for ClauseBound.ParityChecks.emod_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:03:25.070311+00:00
-- url     : https://prove2.me/submissions/465db379-a4e7-4b87-9e10-063dc5597a48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Congr

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Congr
variable {X : Type} [Fintype X] {m : ℕ} (V : X → Finset (Fin m)) (nb r : ℕ)
namespace ClauseBound.ParityChecks
theorem _root_.solution {n : ℕ} {a b : ℤ} (h0 : 0 ≤ a) (ha : a ≤ 2 ^ n) (hab : b ≡ a [ZMOD 2 ^ (n + 1)]) : b % 2 ^ (n + 1) = a := by
  have h : b % 2 ^ (n + 1) = a % 2 ^ (n + 1) := hab
  rw [h, Int.emod_eq_of_lt h0]
  have : (0 : ℤ) < 2 ^ n := by positivity
  rw [pow_succ]
  linarith
end ClauseBound.ParityChecks
