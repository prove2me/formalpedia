-- Prove2me | solution 1 for Eight.ViaGrouping.Table.sum_valF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:12:57.605706+00:00
-- url     : https://prove2.me/submissions/035a63dc-edfa-4f78-91a9-13b971e0765e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_Eight_SecNetworks_Net_lab_toPaperNetwork
import Theorems.Thm_Groundwork_sum_toWord


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
variable {x β : ℕ} {G : Fin K} {θ : Fin K → List Bool}
namespace Eight.ViaGrouping.Table
theorem _root_.solution (h : N.Is P B) {a b : ℕ} (ha : a < g) (hb : b < g) (z z' : List Bool) :
    ∑ y ∈ range (2 ^ N.c ⟨a, ha⟩ ⟨b, hb⟩), valF N.toPaperNetwork a b z (toWord (N.c ⟨a, ha⟩ ⟨b, hb⟩) y) * valF N.toPaperNetwork b a z' (toWord (N.c ⟨a, ha⟩ ⟨b, hb⟩) y) =
      N.toPaperNetwork.Ψ ⟨a, ha⟩ ⟨b, hb⟩ z z' := by
  rw [sum_toWord (N.c ⟨a, ha⟩ ⟨b, hb⟩) fun θ => valF N.toPaperNetwork a b z θ * valF N.toPaperNetwork b a z' θ, Groundwork.Network.Ψ, Net.lab_toPaperNetwork h]
  refine sum_congr rfl fun θ _ => ?_
  rw [show valF N.toPaperNetwork a b z θ = N.toPaperNetwork.f ⟨a, ha⟩ ⟨b, hb⟩ z θ from dif_pos ⟨ha, hb⟩,
    show valF N.toPaperNetwork b a z' θ = N.toPaperNetwork.f ⟨b, hb⟩ ⟨a, ha⟩ z' θ from dif_pos ⟨hb, ha⟩]
end Eight.ViaGrouping.Table
