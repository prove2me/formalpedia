-- Prove2me | solution 1 for Eight.ViaGrouping.not_NSETH_TM_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:20:37.538811+00:00
-- url     : https://prove2.me/submissions/0593d99f-c9c5-4e1b-935b-7d7de3437c06

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_NSETH
import Definitions.Def_Eight_ViaGrouping_CorDefs2
import Definitions.Def_GraphProblems_Host
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_CorNSETH
import Theorems.Thm_Eight_ViaGrouping_tautInNTimeTM_of

set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Paper Turing
namespace Eight.ViaGrouping
theorem _root_.solution (hS : ∀ k : ℕ, 1 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ M : StepMachine (List Bool) Bool, PolyTimeSteps M ∧ ∃ c : ℕ, Decides M k δ c) : ¬ NSETH_TM := by
  intro h
  obtain ⟨k, hk, hn⟩ := h (1 / 2) (by norm_num)
  obtain ⟨M, hp, c, hM⟩ := hS k hk ((1 - 1 / 2) / 2) (by norm_num)
  exact hn (tautInNTimeTM_of k (by norm_num) hp hM)
end Eight.ViaGrouping
