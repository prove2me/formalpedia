-- Prove2me | solution 1 for CircuitLowerBound.Clause.Fw_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:53:41.209795+00:00
-- url     : https://prove2.me/submissions/190b7807-8d57-4543-9e90-eb73de6e49ac

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_CircuitLowerBound_Clause_fld_val
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks
namespace CircuitLowerBound.Clause
theorem _root_.solution {v : ℕ → Bool} {n rb kbm nf : ℕ} {tb : List TCl} (h : Obeys v (n + 2 + rb * tb.length) (fldG n rb kbm nf tb)) (hZ : v n = false) {r : ℕ}
    (hE : ∀ k < tb.length, v (Ew n rb k) = decide (r = k)) {ι f : ℕ} (hι : ι < 3) (hf : f < nf) :
    v (Fw n rb tb.length nf ι f) = fbit kbm (litI (tb.getD r zeroCl) ι) f := by
  have ha : ι * nf + f < 3 * nf := by nlinarith
  have h1 := fld_val h hZ hE ha
  have e1 : (ι * nf + f) / nf = ι := by rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hf, Nat.add_zero]
  have e2 : (ι * nf + f) % nf = f := by rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hf]
  rw [e1, e2] at h1
  exact h1
end CircuitLowerBound.Clause
