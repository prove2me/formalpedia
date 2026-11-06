-- Prove2me | solution 1 for CircuitLowerBound.Pack.vidx_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:30:48.678938+00:00
-- url     : https://prove2.me/submissions/8008d126-4497-4924-8b90-d58ac78f20c2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Pack
import Theorems.Thm_CircuitLowerBound_Pack_tval_le
import Theorems.Thm_CircuitLowerBound_Pack_qval_lt
import Theorems.Thm_CircuitLowerBound_Pack_bt_le_bq
import Theorems.Thm_CircuitLowerBound_Pack_lam_le_bq

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP
open CircuitLowerBound.Pack
variable {e : MCode} {L P : ℕ}
namespace CircuitLowerBound.Pack
theorem _root_.solution (hg : GoodCode e) (hF : Fits e L P) {c : TCl} (hc : c ∈ tab e) {l : TLit} (hl : l ∈ lits c) {t q : ℕ} (ht : t < 2 ^ bt e L)
    (hq : q < 2 ^ bq e L) :
    vidx e L P t q l = (l.1 * 2 ^ (bt e L + 1) + tval (bt e L) t l.2.1) * 2 ^ (bq e L + 1) + (qval P q l.2.2.1 + l.2.2.2.1) ∧
      tval (bt e L) t l.2.1 < 2 ^ (bt e L + 1) ∧ qval P q l.2.2.1 + l.2.2.2.1 < 2 ^ (bq e L + 1) := by
  obtain ⟨-, h2, h3⟩ := hg c hc l hl
  have h4 := tval_le ht l.2.1
  have h5 := qval_lt (P := P) hq (by have := hF.2; have := bt_le_bq e L; omega) l.2.2.1
  have h6 := lam_le_bq e L
  have h7 : 0 < 2 ^ bt e L := by positivity
  have hA : tval (bt e L) t l.2.1 < 2 ^ (bt e L + 1) := by rw [pow_succ]; omega
  have hB : qval P q l.2.2.1 + l.2.2.2.1 < 2 ^ (bq e L + 1) := by rw [pow_succ]; omega
  exact ⟨by rw [vidx, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt hB], hA, hB⟩
end CircuitLowerBound.Pack
