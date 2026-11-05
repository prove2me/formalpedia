-- Prove2me | solution 1 for Eight.ViaGrouping.lbLen_eq_Y
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:04:12.511189+00:00
-- url     : https://prove2.me/submissions/55ede9b9-1533-49cb-bddc-1aa3226b88e1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Definitions.Def_Eight_SecNetworks_Grouping
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Search
import Theorems.Thm_Eight_ViaGrouping_presentsP
import Theorems.Thm_Groundwork_Network_merge_c
import Theorems.Thm_Groundwork_Prog_NetE_lbLen_eq


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
variable {C : Type} [HasSize C] {Np : Procs C} {c : C} {g K : ℕ} {N : Net g} {P B τ S : ℕ}
namespace Eight.ViaGrouping
theorem _root_.solution (hK0 : 0 < K) (h : IsNetworkP Np c N P B τ S) (x : ℕ) {γ γ' : Fin K} (hne : γ ≠ γ') :
    lbLen K g Np.toPaperNetwork c x γ.val γ'.val = Y N.c (Paper.grouping hK0 x) γ γ' := by
  rw [lbLen_eq _ hK0 (presentsP h) x hne, Groundwork.Network.merge_c]
  rfl
end Eight.ViaGrouping
