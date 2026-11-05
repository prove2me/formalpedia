-- Prove2me | solution 1 for CircuitLowerBound.Tab.pref_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:31:28.893174+00:00
-- url     : https://prove2.me/submissions/fb20fbec-ae53-4519-a974-5013e88fd993

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Spec
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Tab
open ENP Turing
namespace CircuitLowerBound.Tab
theorem _root_.solution {α : Type} (d : ℕ) : ∀ S : List α, pref (List.ofFn fun j : Fin d => S[j.val]?) = S.take d := by
  induction d with
  | zero => intro S; simp [pref]
  | succ d ih =>
    intro S
    rw [List.ofFn_succ]
    cases S with
    | nil => simp [pref]
    | cons a S => simpa [pref] using ih S
end CircuitLowerBound.Tab
