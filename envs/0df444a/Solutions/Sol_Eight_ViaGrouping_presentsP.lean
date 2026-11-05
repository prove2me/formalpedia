-- Prove2me | solution 1 for Eight.ViaGrouping.presentsP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:56:54.635917+00:00
-- url     : https://prove2.me/submissions/17c69ee0-7454-4fe5-828f-b2ed3d611669

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Definitions.Def_Eight_SecNetworks_Grouping
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Search
import Theorems.Thm_Eight_SecNetworks_presents_toPaperNetwork
import Theorems.Thm_PaddedDescent_F_cap_eq


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
variable {C : Type} [HasSize C] {Np : Procs C} {c : C} {g K : ℕ} {N : Net g} {P B τ S : ℕ}
namespace Eight.ViaGrouping
theorem _root_.solution (h : IsNetworkP Np c N P B τ S) : Np.toPaperNetwork.Presents c N.toPaperNetwork (2 * τ + 1) (S + (size c + 2 * size g + 4 * P + 6)) :=
  presents_toPaperNetwork (Np := { Np with B := fun _ => B }) (c := c) (N := N) (P := P) (B := B) (τ := τ) (S := S)
    ⟨h.is, h.τ_pos, ⟨h.given.P_eq, rfl, h.given.len_eq, h.given.cap_eq, h.given.mem_runs, h.given.W_runs, h.given.Ψ_runs, h.given.f_runs⟩⟩
end Eight.ViaGrouping
