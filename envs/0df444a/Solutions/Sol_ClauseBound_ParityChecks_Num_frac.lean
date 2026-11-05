-- Prove2me | solution 1 for ClauseBound.ParityChecks.Num.frac
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:20:55.939297+00:00
-- url     : https://prove2.me/submissions/e7083975-8fb6-431b-88f2-02e72142cf86

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Approx
import Definitions.Def_ClauseBound_ParityChecks_Num

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m))
open ClauseBound.ParityChecks.Num
namespace ClauseBound.ParityChecks.Num
theorem _root_.solution (nb a c n : ℕ) (hnb : 1 ≤ nb) (hc : c ≤ n) :
    (2 : ℚ) ^ a / (1 + pr nb) ^ c = ((2 ^ a * nb ^ c * (nb + 1) ^ (n - c) : ℕ) : ℚ) / ((nb : ℚ) + 1) ^ n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
  have h0 : (nb : ℚ) ≠ 0 := by exact_mod_cast (by omega : nb ≠ 0)
  have h1 : (nb : ℚ) + 1 ≠ 0 := by positivity
  have h2 : (1 : ℚ) + 1 / nb = (nb + 1) / nb := by field_simp
  rw [Nat.add_sub_cancel_left, pow_add]
  unfold pr
  push_cast
  rw [h2, div_pow]
  field_simp
end ClauseBound.ParityChecks.Num
