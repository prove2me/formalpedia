-- Prove2me | solution 1 for ExplicitCost.size_unary_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:11:09.123865+00:00
-- url     : https://prove2.me/submissions/5894e415-6fb2-4a1a-87d3-48fad5d930d9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallParts
import Definitions.Def_ClauseBound_Gen_RateAux
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ParentSize
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_unit
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution (n : ℕ) : size (unary n) = 2 * n + 1 := by
  unfold unary
  rw [size_list, List.map_replicate, List.sum_replicate, size_unit, smul_eq_mul]
  omega
end ExplicitCost
