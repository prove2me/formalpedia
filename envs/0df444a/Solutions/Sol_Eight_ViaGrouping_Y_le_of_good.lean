-- Prove2me | solution 1 for Eight.ViaGrouping.Y_le_of_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:05:24.010899+00:00
-- url     : https://prove2.me/submissions/52947d63-4fde-490e-b396-c633a9336a84

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Definitions.Def_Eight_SecNetworks_Grouping
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Search
import Theorems.Thm_Groundwork_Colouring_le_beta


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
variable {C : Type} [HasSize C] {Np : Procs C} {c : C} {g K : ℕ} {N : Net g} {P B τ S : ℕ}
namespace Eight.ViaGrouping
theorem _root_.solution (hK0 : 0 < K) {χ : Fin g → Fin K} (hχ : Good N.c P χ) {γ γ' : Fin K} (hne : γ ≠ γ') : Y N.c χ γ γ' ≤ Paper.groupedLength K g N.U P :=
  Colouring.le_beta hK0 (hχ.G2 γ γ' hne)
end Eight.ViaGrouping
