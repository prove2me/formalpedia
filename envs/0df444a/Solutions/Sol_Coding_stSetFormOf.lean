-- Prove2me | solution 1 for Coding.stSetFormOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:07:45.8541+00:00
-- url     : https://prove2.me/submissions/e6a0f2c0-78ea-4bb0-99d9-505347988cdf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_Defs
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Ring
import Definitions.Def_Coding_Sets
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open Coding
open Finset
namespace Coding
theorem _root_.solution : StSetFormOf := by
  intro HW H2 δ hδ
  obtain ⟨M, c, hfin, h⟩ := H2 δ hδ
  refine ⟨M, c, hfin, fun n Φ φ hφ => ?_⟩
  obtain ⟨h3, -, -, hsat⟩ := (HW n Φ).2 φ hφ
  obtain ⟨b, t, hb, ht, hh⟩ := h n φ h3
  exact ⟨b, t, hb.trans hsat, ht, hh⟩
end Coding
