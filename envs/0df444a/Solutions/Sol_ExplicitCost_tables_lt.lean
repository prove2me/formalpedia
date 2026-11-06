-- Prove2me | solution 1 for ExplicitCost.tables_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:55:46.085386+00:00
-- url     : https://prove2.me/submissions/db1f336a-18b0-42f0-b353-c4410ef41a38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_CountedRecursion_SolverStages
import Definitions.Def_CountedRecursion_LevelNumbers
import Definitions.Def_Printed_GroupingEntry
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverPattern
import Theorems.Thm_ExplicitCost_K_succ_mul
import Theorems.Thm_ExplicitCost_readTables_setting
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {x₀ l : ℕ} {a : Ctx} {f : TableQuery → Option Ans} (hF : Fits x₀ a f) (hl : cLev a = l + 1) :
    ∀ w < Levels.Gen.g x₀ l * Levels.Gen.g x₀ l, ∀ z ∈ words ((Levels.Gen.g x₀ l * Levels.Gen.g x₀ l - 1) * cLam a), |readTables f w z| < 2 ^ cB a := by
  obtain ⟨_, _, W, hW, rfl⟩ := hF
  rw [hl, K_succ_mul] at hW ⊢
  intro w hw z hz
  rw [readTables_setting W hw (mem_words.1 hz)]
  exact hW w hw z hz
end ExplicitCost
