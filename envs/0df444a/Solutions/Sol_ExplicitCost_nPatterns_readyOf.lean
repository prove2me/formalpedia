-- Prove2me | solution 1 for ExplicitCost.nPatterns_readyOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:40:55.306087+00:00
-- url     : https://prove2.me/submissions/894b415f-0d6b-4129-80d2-ff38653c6325

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_ClauseBound_Gen_Pick
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CallParts
import Theorems.Thm_ExplicitCost_rG_readyOf
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable (D : PiecesCounted.Data) (x₀ : ℕ) (h : Head) {l : ℕ}
namespace ExplicitCost
theorem _root_.solution (hl : hLev h = l + 1) : nPatterns (readyOf D x₀ h) = #(D.fam (hLam h)).I ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) := by
  unfold nPatterns rRect
  rw [rG_readyOf D x₀ h hl]
  change ((D.fam (hLam h)).I.sort).length ^ _ = _
  rw [Finset.length_sort]
end ExplicitCost
