-- Prove2me | solution 1 for Eight.ViaGrouping.lamP_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:04:56.244201+00:00
-- url     : https://prove2.me/submissions/3403ce7b-1334-4109-aaf3-750387ecf527

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Definitions.Def_Eight_SecNetworks_Grouping
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Search
import Theorems.Thm_Eight_ViaGrouping_Uc_eq_U

set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
variable {C : Type} [HasSize C] {Np : Procs C} {c : C} {g K : ℕ} {N : Net g} {P B τ S : ℕ}
namespace Eight.ViaGrouping
theorem _root_.solution (h : IsNetworkP Np c N P B τ S) (x : ℕ) : lamP K g Np (c, x) = Paper.groupedLength K g N.U P := by
  unfold lamP
  rw [Uc_eq_U h, h.given.P_eq]
end Eight.ViaGrouping
