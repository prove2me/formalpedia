-- Prove2me | solution 1 for Eight.ViaGrouping.Table.lbLen_eq_Y
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:35:57.634122+00:00
-- url     : https://prove2.me/submissions/339b7122-d244-4892-bb21-6f4f83a9b33e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_Eight_ViaGrouping_Table_isPaperNetwork
import Theorems.Thm_Groundwork_Network_merge_c
import Theorems.Thm_Groundwork_Prog_NetE_lbLen_eq


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
variable {x β : ℕ} {G : Fin K} {θ : Fin K → List Bool}
namespace Eight.ViaGrouping.Table
theorem _root_.solution (h : IsNetworkP Np c N P B τ S) (hK0 : 0 < K) (x : ℕ) {γ γ' : Fin K} (hne : γ ≠ γ') :
    lbLen K g Np.toPaperNetwork c x γ.val γ'.val = Y N.c (Paper.grouping hK0 x) γ γ' := by
  rw [lbLen_eq Np.toPaperNetwork hK0 (isPaperNetwork h).presented x hne, Groundwork.Network.merge_c]
  rfl
end Eight.ViaGrouping.Table
