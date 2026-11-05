-- Prove2me | solution 1 for Eight.ViaGrouping.Table.cap_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:12:28.711479+00:00
-- url     : https://prove2.me/submissions/64361fcc-2cf9-45b6-9aca-b314491cbae3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_PaddedDescent_F_cap_eq


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
omit [HasSize C]
namespace Eight.ViaGrouping.Table
theorem _root_.solution (h : IsNetworkP Np c N P B τ S) (a b : Fin g) : Np.cap c a b = Np.cap c b a := by
  by_cases hab : a = b
  · rw [hab]
  · rw [h.given.cap_eq _ _ hab, h.given.cap_eq _ _ (Ne.symm hab), h.is.c_symm]
end Eight.ViaGrouping.Table
