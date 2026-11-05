-- Prove2me | solution 1 for Eight.ViaGrouping.Table.isNetwork
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:24:49.11145+00:00
-- url     : https://prove2.me/submissions/50ba0b4a-8b41-4bd6-99ef-3edc0e3556ea

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_PaddedDescent_F_cap_eq


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
omit [HasSize C]
namespace Eight.ViaGrouping.Table
theorem _root_.solution (h : IsNetworkP Np c N P B τ S) : IsNetwork { Np with B := fun _ => B } c N P B τ S :=
  ⟨h.is, h.τ_pos, ⟨h.given.P_eq, rfl, h.given.len_eq, h.given.cap_eq, h.given.mem_runs, h.given.W_runs, h.given.Ψ_runs, h.given.f_runs⟩⟩
end Eight.ViaGrouping.Table
