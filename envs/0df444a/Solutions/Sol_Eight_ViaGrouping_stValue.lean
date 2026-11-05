-- Prove2me | solution 1 for Eight.ViaGrouping.stValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:32:41.333601+00:00
-- url     : https://prove2.me/submissions/a70d1675-13ff-481d-9f77-6c5f84aa4b25

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_Eight_ViaGrouping_Table_isPaperNetwork
import Theorems.Thm_Eight_SecNetworks_Net_value_toPaperNetwork
import Theorems.Thm_Groundwork_Network_merge_c
import Theorems.Thm_Paper_grouped_value


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Table
namespace Eight.ViaGrouping
theorem _root_.solution : StValue := by
  intro K g hK0 C _ Np c N P B τ S h x L hY
  rw [Paper.grouped_value Np.toPaperNetwork hK0 (isPaperNetwork h) x L fun γ γ' hne => by
    rw [Groundwork.Network.merge_c]
    exact hY γ γ' hne]
  exact Net.value_toPaperNetwork h.is
end Eight.ViaGrouping
