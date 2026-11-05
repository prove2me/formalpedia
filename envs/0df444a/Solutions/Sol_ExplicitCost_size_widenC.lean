-- Prove2me | solution 1 for ExplicitCost.size_widenC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:49:04.170567+00:00
-- url     : https://prove2.me/submissions/6c088c44-0ffb-4118-82a3-dde62815248b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_Mirror
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_SameRuns
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_unit
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_unit


section
namespace ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (K g : ℕ)
private theorem size_unary (n : ℕ) : size (unary n) = 2 * n + 1 := by
  rw [unary, size_list, List.map_replicate, List.sum_replicate, size_unit, smul_eq_mul]
  omega
end ExplicitCost
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
variable (K g : ℕ)
namespace ExplicitCost
theorem _root_.solution (c : NetInput) : size (widenC K g c) = size c + (2 * K + 2 * g + 2) := by
  change size (unary K) + size (unary g) + size c = _
  rw [size_unary, size_unary]
  omega
end ExplicitCost
