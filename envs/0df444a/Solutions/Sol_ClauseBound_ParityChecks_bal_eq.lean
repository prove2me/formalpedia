-- Prove2me | solution 1 for ClauseBound.ParityChecks.bal_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:00:01.082834+00:00
-- url     : https://prove2.me/submissions/81356c1b-dbb1-4dfe-a5d3-d571caa0ecec

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
theorem _root_.solution {β : ℕ} (hβ : 1 ≤ β) {a b : ℤ} (ha : |a| < 2 ^ (β - 1)) (hab : b ≡ a [ZMOD 2 ^ β]) : bal β b = a := by
  have hN : (2 : ℤ) ^ β = 2 * 2 ^ (β - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h1 := abs_lt.1 ha
  have h2 : (b + 2 ^ (β - 1)) % 2 ^ β = (a + 2 ^ (β - 1)) % 2 ^ β := hab.add_right _
  unfold bal
  rw [h2, Int.emod_eq_of_lt (by linarith) (by rw [hN]; linarith)]
  ring
end ClauseBound.ParityChecks
