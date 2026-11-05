-- Prove2me | solution 1 for Eight.ViaGrouping.Table.natAbs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:11:42.12513+00:00
-- url     : https://prove2.me/submissions/451dd64c-f572-46ec-8e00-55bc68b1ab99

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table

set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
namespace Eight.ViaGrouping.Table
theorem _root_.solution {z : ℤ} {n : ℕ} (h : |z| ≤ 2 ^ n) : z.natAbs ≤ 2 ^ n := by
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h
end Eight.ViaGrouping.Table
