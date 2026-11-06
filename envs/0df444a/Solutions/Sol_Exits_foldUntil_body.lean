-- Prove2me | solution 1 for Exits.foldUntil_body
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:27:10.809975+00:00
-- url     : https://prove2.me/submissions/81168023-5dd7-4299-af42-c250ba6b4b71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_Tested
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_Exits_Runs
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono


set_option autoImplicit false
section
section
open Exits
open Finset Groundwork Groundwork.Stepped
open Groundwork.Sparsify (leaves)
variable {α β γ τ ν : Type}
variable [HasSize τ] [HasSize γ] {start : α → Option τ} {nxt : τ → Option τ} {M : Stepped τ β} {g : γ → τ → β → γ} {stop : γ → Bool} {c₀ : α → γ}
namespace Exits
theorem _root_.solution {x : τ} {c r : γ} {b : β} {s : M.σ} {t T Sm S : ℕ} (h : M.Reaches Sm b s t) (hS : size x + (size c + Sm) + 1 ≤ S)
    (hr : (foldUntil start nxt M g stop c₀).Reaches S r (foldGo M (g c x b) (if stop (g c x b) then none else nxt x)) T) :
    (foldUntil start nxt M g stop c₀).Reaches S r (.inl (x, c, s)) (t + 1 + T) := by
  induction h with
  | @halt s t ho hs =>
    have e : (foldUntil start nxt M g stop c₀).step (.inl (x, c, s)) = foldGo M (g c x b) (if stop (g c x b) then none else nxt x) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have : (foldUntil start nxt M g stop c₀).Reaches S r (.inl (x, c, s)) (T + 1) :=
      .step rfl (by change size x + (size c + size s) + 1 ≤ _; omega) (e ▸ hr)
    exact this.mono (by omega) le_rfl
  | @step s t ho hs _ ih =>
    have e : (foldUntil start nxt M g stop c₀).step (.inl (x, c, s)) = .inl (x, c, M.step s) := by
      change (match M.out s with | some b => _ | none => _) = _
      rw [ho]
    have : (foldUntil start nxt M g stop c₀).Reaches S r (.inl (x, c, s)) (t + 1 + T + 1) :=
      .step rfl (by change size x + (size c + size s) + 1 ≤ _; omega) (e ▸ ih)
    exact this.mono (by omega) le_rfl
end Exits
