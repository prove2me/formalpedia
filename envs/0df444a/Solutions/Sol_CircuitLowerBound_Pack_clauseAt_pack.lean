-- Prove2me | solution 1 for CircuitLowerBound.Pack.clauseAt_pack
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:15:16.004286+00:00
-- url     : https://prove2.me/submissions/b4047e08-9c71-44b6-96a7-693a383c2998

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Pack
import Theorems.Thm_CircuitLowerBound_Pack_div_pack
import Theorems.Thm_CircuitLowerBound_Pack_mod_pack

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP
open CircuitLowerBound.Pack
variable {e : MCode} {L P : ℕ}
namespace CircuitLowerBound.Pack
theorem _root_.solution (e : MCode) (L P : ℕ) {r t q : ℕ} (ht : t < 2 ^ bt e L) (hq : q < 2 ^ bq e L) :
    clauseAt e L P ((r * 2 ^ bt e L + t) * 2 ^ bq e L + q) = (lits ((tab e).getD r zeroCl)).map (litAt e L P t q) := by
  have h1 : ((r * 2 ^ bt e L + t) * 2 ^ bq e L + q) / 2 ^ bq e L = r * 2 ^ bt e L + t := div_pack hq
  have h2 : ((r * 2 ^ bt e L + t) * 2 ^ bq e L + q) % 2 ^ bq e L = q := mod_pack hq
  have h3 : ((r * 2 ^ bt e L + t) * 2 ^ bq e L + q) / 2 ^ (bt e L + bq e L) = r := by
    rw [Nat.add_comm (bt e L), pow_add, ← Nat.div_div_eq_div_mul, h1, div_pack ht]
  rw [clauseAt, h1, h2, h3, mod_pack ht]
  rfl
end CircuitLowerBound.Pack
