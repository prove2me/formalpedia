-- Prove2me | solution 1 for Eight.ViaGrouping.Uc_eq_U
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:00:07.513704+00:00
-- url     : https://prove2.me/submissions/fa7b135b-b8ec-485f-bdad-970e4288ac9f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Definitions.Def_Eight_SecNetworks_Grouping
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Search
import Theorems.Thm_Eight_ViaGrouping_presentsP
import Theorems.Thm_Groundwork_Prog_NetE_Uc_eq


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
variable {C : Type} [HasSize C] {Np : Procs C} {c : C} {g K : ℕ} {N : Net g} {P B τ S : ℕ}
namespace Eight.ViaGrouping
theorem _root_.solution (h : IsNetworkP Np c N P B τ S) : Uc g Np.toPaperNetwork c = N.U := Uc_eq _ (presentsP h)
end Eight.ViaGrouping
