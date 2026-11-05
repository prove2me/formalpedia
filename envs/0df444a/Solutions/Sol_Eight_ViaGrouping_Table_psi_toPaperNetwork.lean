-- Prove2me | solution 1 for Eight.ViaGrouping.Table.psi_toPaperNetwork
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:20:23.894524+00:00
-- url     : https://prove2.me/submissions/ac6b8894-1744-4a74-9522-4b42480d648a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_P2M_Eight_SecNetworks_Net___toPaperNetwork_89d84f9cfc58
import Theorems.Thm_P2M_Eight_SecNetworks_Net___toPaperNetwork_eq_zero_529fe2c28428


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
variable {x β : ℕ} {G : Fin K} {θ : Fin K → List Bool}
namespace Eight.ViaGrouping.Table
theorem _root_.solution (h : N.Is P B) {a b : Fin g} (hab : a ≠ b) (z z' : List Bool) :
    N.toPaperNetwork.Ψ a b z z' = if z ∈ N.S a then (if z' ∈ N.S b then N.Ψ a b z z' else 0) else 0 := by
  by_cases hz : z ∈ N.S a
  · by_cases hz' : z' ∈ N.S b
    · rw [if_pos hz, if_pos hz', Net.Ψ_toPaperNetwork h hab hz hz']
    · rw [if_pos hz, if_neg hz', Net.Ψ_toPaperNetwork_eq_zero fun hh => hz' hh.2]
  · rw [if_neg hz, Net.Ψ_toPaperNetwork_eq_zero fun hh => hz hh.1]
end Eight.ViaGrouping.Table
