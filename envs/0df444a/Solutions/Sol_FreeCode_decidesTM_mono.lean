-- Prove2me | solution 1 for FreeCode.decidesTM_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:14:16.933205+00:00
-- url     : https://prove2.me/submissions/a360ec7d-0ed8-45c6-9ac7-4950fa20e483

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Code
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_FreeCode_Behind
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Paper SplitSat
namespace FreeCode
theorem _root_.solution {k : ℕ} {M : Turing.TM2ComputableAux Bool Bool} {t t' : ℕ → ℕ} (ht : ∀ n, t n ≤ t' n) (h : SatFree.DecidesTM k M t) :
    SatFree.DecidesTM k M t' := fun n φ h3 => by
  obtain ⟨b, hb, ⟨ev⟩⟩ := h n φ h3
  exact ⟨b, hb, ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (ht n)⟩⟩⟩
end FreeCode
