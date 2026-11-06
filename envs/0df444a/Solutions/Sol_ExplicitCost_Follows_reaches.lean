-- Prove2me | solution 1 for ExplicitCost.Follows.reaches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:21:52.094383+00:00
-- url     : https://prove2.me/submissions/05c9f9f2-1b68-42f3-a7a0-53ff99a1c718

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_Mirror
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines
variable {Q A α α' α₁ α₁' α₂ α₂' β β' γ τ τ' : Type}
namespace ExplicitCost
namespace Follows
theorem _root_.solution {M : QueryMachine Q A α β} {M' : QueryMachine Q A α' β} {w : α → α'} {d : ℕ} {φ : M.σ → M'.σ} (h : Follows M M' w d φ) {O : Q → Option A} {S own : ℕ} {b : β} {s : M.σ} {L : List Q}
    (r : M.Reaches O S b s own L) : M'.Reaches O (S + d) b (φ s) own L := by
  induction r with
  | halt ho hs => exact .halt ((h.out _).trans ho) ((h.size _).trans (Nat.add_le_add_right hs d))
  | step ho ha hs _ ih => exact .step ((h.out _).trans ho) ((h.ask _).trans ha) ((h.size _).trans (Nat.add_le_add_right hs d)) (by rw [h.step]; exact ih)
  | query ho ha hv hs _ ih => exact .query ((h.out _).trans ho) ((h.ask _).trans ha) hv ((h.size _).trans (Nat.add_le_add_right hs d)) (by rw [h.resume]; exact ih)
end Follows
end ExplicitCost
