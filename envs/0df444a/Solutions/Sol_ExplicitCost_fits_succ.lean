-- Prove2me | solution 1 for ExplicitCost.fits_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:30:07.422623+00:00
-- url     : https://prove2.me/submissions/00885068-511c-4c1c-a18a-d72b9549202d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_ClauseBound_Gen_Pick
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CallParts
import Theorems.Thm_ExplicitCost_answersOf_readTables
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
    1 ≤ cLam a ∧ 1 ≤ cB a ∧ (∀ w < Levels.Gen.g x₀ l * Levels.Gen.g x₀ l, ∀ z ∈ words ((Levels.Gen.g x₀ l * Levels.Gen.g x₀ l - 1) * cLam a), |readTables f w z| < 2 ^ cB a) ∧
      f = answersOf (Levels.Gen.g x₀ l * Levels.Gen.g x₀ l) (cLam a) (readTables f) := by
  obtain ⟨h1, h2, W, hW, rfl⟩ := hF
  have e : Levels.Gen.K x₀ (cLev a) = Levels.Gen.g x₀ l * Levels.Gen.g x₀ l := by
    rw [hl]
    exact sq (Levels.Gen.g x₀ l)
  rw [e] at hW ⊢
  refine ⟨h1, h2, fun w hw z hz => ?_, (answersOf_readTables _ _ _).symm⟩
  rw [readTables_setting _ hw (mem_words.1 hz)]
  exact hW w hw z hz
end ExplicitCost
