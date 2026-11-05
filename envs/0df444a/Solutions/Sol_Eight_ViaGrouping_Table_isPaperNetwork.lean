-- Prove2me | solution 1 for Eight.ViaGrouping.Table.isPaperNetwork
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:28:21.900267+00:00
-- url     : https://prove2.me/submissions/d3349067-061f-48ab-8687-1fa5deb2ab63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_Eight_ViaGrouping_Table_isNetwork
import Theorems.Thm_Eight_SecNetworks_Net_sized_toPaperNetwork
import Theorems.Thm_Eight_SecNetworks_presents_toPaperNetwork


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
namespace Eight.ViaGrouping.Table
theorem _root_.solution (h : IsNetworkP Np c N P B τ S) :
    Paper.IsNetwork Np.toPaperNetwork c N.toPaperNetwork P B (2 * τ + 1) (S + (size c + 2 * size g + 4 * P + 6)) :=
  have hp := presents_toPaperNetwork (isNetwork h)
  ⟨Net.sized_toPaperNetwork h.is, hp⟩
end Eight.ViaGrouping.Table
