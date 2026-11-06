-- Prove2me | solution 1 for ExplicitCost.dig_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:47:57.575366+00:00
-- url     : https://prove2.me/submissions/e74fa17f-f104-4e95-aea0-81c62f6f3b44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_ParentNumbers
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RowWeightRun
import Theorems.Thm_ClauseBound_Alg_GridNet_digG_lt
import Theorems.Thm_ExplicitCost_card_I_pos
import Theorems.Thm_ExplicitCost_indexAt_mem


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {D : PiecesCounted.Data} {c g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}
namespace ExplicitCost
theorem _root_.solution {ρ : ℝ} {x₀ : ℕ} (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) (g : ℕ) (tr : Bool) (y q κ : ℕ) : indexAt D lam (digG (piecesOf D c) g tr 0 lam y q κ) ∈ (D.fam lam).I :=
  indexAt_mem D lam (digG_lt (P := piecesOf D c) (h := 0) (ℓ := lam) (card_I_pos hS.is hlam) g tr y q κ)
end ExplicitCost
