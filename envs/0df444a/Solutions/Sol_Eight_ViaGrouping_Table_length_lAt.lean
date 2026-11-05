-- Prove2me | solution 1 for Eight.ViaGrouping.Table.length_lAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:12:36.446037+00:00
-- url     : https://prove2.me/submissions/0c7f1b67-ee73-4100-becc-eee59fc0838e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_cut_eq_getD_beq
import Theorems.Thm_Groundwork_length_cut_of_le
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
omit [HasSize C]
namespace Eight.ViaGrouping.Table
theorem _root_.solution (Nq : PNet C) {x G G' : ℕ} {θ : List Bool} {p : ℕ × ℕ} (hp : p ∈ prs K g x G G') (hθ : lbLen K g Nq c x G G' ≤ θ.length) :
    (lAt K g Nq c x G G' θ p).length = Nq.cap c p.1 p.2 := by
  unfold lAt lbLens
  rw [← cut_eq_getD_beq (fun p : ℕ × ℕ => Nq.cap c p.1 p.2)]
  exact length_cut_of_le _ _ _ _ hθ hp
end Eight.ViaGrouping.Table
