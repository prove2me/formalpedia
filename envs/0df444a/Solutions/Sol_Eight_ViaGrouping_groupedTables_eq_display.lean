-- Prove2me | solution 1 for Eight.ViaGrouping.groupedTables_eq_display
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:28:22.998828+00:00
-- url     : https://prove2.me/submissions/b616f76b-9eb7-43ff-a040-8a7442c3aa4c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Table
import Definitions.Def_Eight_SecNetworks_Tables
import Definitions.Def_Eight_SecNetworks_Clique
import Definitions.Def_Eight_ViaGrouping_Display
import Theorems.Thm_Eight_SecNetworks_tables_eq
import Theorems.Thm_Eight_ViaGrouping_Table_isNetwork
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
variable {C : Type} [HasSize C] {g K : ℕ}
variable {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
namespace Eight.ViaGrouping
theorem _root_.solution (h : IsNetworkP Np c N P B τ S) (hK0 : 0 < K) (x L : ℕ) (hL : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L)
    (γ : Fin K) (Θ : Fin K → List Bool) (hΘ : ∀ γ', γ' ≠ γ → (Θ γ').length = L) :
    Paper.groupedTables Np.toPaperNetwork c N.toPaperNetwork hK0 x L γ Θ = display Np c N hK0 x γ Θ :=
  tables_eq (Table.isNetwork h) hK0 x L hL γ Θ hΘ
end Eight.ViaGrouping
