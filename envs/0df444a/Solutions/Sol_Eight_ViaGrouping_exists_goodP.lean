-- Prove2me | solution 1 for Eight.ViaGrouping.exists_goodP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:02:21.684145+00:00
-- url     : https://prove2.me/submissions/2f1bc1d3-4cb0-4981-98df-2e9c047a31d2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Definitions.Def_Eight_SecNetworks_Grouping
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Search
import Theorems.Thm_Eight_ViaGrouping_goodP_iff
import Theorems.Thm_Eight_ViaGrouping_grouping_number
import Theorems.Thm_Eight_SecNetworks_groupingFacts


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
variable {C : Type} [HasSize C] {Np : Procs C} {c : C} {g K : ℕ} {N : Net g} {P B τ S : ℕ}
namespace Eight.ViaGrouping
theorem _root_.solution (hK : 2 ≤ K) {N : Net (3 * K ^ 8)} (h : IsNetworkP Np c N P B τ S) : ∃ x < K ^ (3 * K ^ 8), goodP K (3 * K ^ 8) Np (c, x) = true := by
  have hK0 : 0 < K := by omega
  obtain ⟨χ, hχ⟩ := groupingFacts.exists_good K P N.c hK h.is.c_symm h.is.i
  obtain ⟨x, hx, rfl⟩ := grouping_number hK0 χ
  exact ⟨x, hx, (goodP_iff hK0 h x).2 hχ⟩
end Eight.ViaGrouping
