-- Prove2me | solution 1 for ExplicitCost.label_le_net
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:13:35.545675+00:00
-- url     : https://prove2.me/submissions/d8e4d7c3-ac4d-4d18-8b09-17e4169a172d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CaseTwo
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LabelCrude
import Theorems.Thm_ExplicitCost_total_le
import Theorems.Thm_ExplicitCost_label_le_of

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) (l : ℕ) {lam : ℕ} (hlam : 1 ≤ lam) (y : ℕ) (tr : Bool) (W : ℕ → List Bool → ℤ) :
    AppRunningTime.Lof (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) ((1 : ℝ) / (2 ^ (l + 5) : ℕ)) (Levels.Gen.g x₀ l ^ 3 * lam) (patternNet D c (Levels.Gen.g x₀ l) tr lam y W).U ≤ Levels.Gen.g x₀ l ^ 4 * lam + 1 :=
  label_le_of x₀ l lam _ hS.x₀_ge (total_le hS _ hlam y tr W)
end ExplicitCost
