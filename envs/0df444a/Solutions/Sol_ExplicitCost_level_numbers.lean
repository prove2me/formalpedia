-- Prove2me | solution 1 for ExplicitCost.level_numbers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:21:03.878292+00:00
-- url     : https://prove2.me/submissions/f20b8916-dc1c-4de2-90d5-d24062e080c4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_ClauseBound_Gen_Pick
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CallParts
import Theorems.Thm_ClauseBound_Gen_Pick_K_le_g
import Theorems.Thm_ClauseBound_Gen_Seq_two_le_K
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {x₀ : ℕ} (hx : 18 ≤ x₀) (l : ℕ) : 2 ≤ Levels.Gen.K x₀ l ∧ Levels.Gen.K x₀ l ≤ Levels.Gen.g x₀ l ∧ 2 ≤ Levels.Gen.g x₀ l :=
  ⟨ClauseBound.Gen.Seq.two_le_K x₀ l hx, ClauseBound.Gen.Pick.K_le_g x₀ l, (ClauseBound.Gen.Seq.two_le_K x₀ l hx).trans (ClauseBound.Gen.Pick.K_le_g x₀ l)⟩
end ExplicitCost
