-- Prove2me | solution 1 for ExplicitCost.sizeBound_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:23:49.302916+00:00
-- url     : https://prove2.me/submissions/8aa9e9b2-1f36-40c2-9a37-810b425bc99d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_Printed_Coding
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_StepMachines_Prog_SideBasics
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_EndBounds
import Theorems.Thm_ExplicitCost_base_ge

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
namespace ExplicitCost
theorem _root_.solution {x₀ : ℕ} (hx : 18 ≤ x₀) (l : ℕ) {lam B : ℕ} (hlam : 1 ≤ lam) (hB : 1 ≤ B) {C C' : ℕ} (h : C ≤ C') : sizeBound x₀ C l lam B ≤ sizeBound x₀ C' l lam B := by
  have hX := base_ge hx l hlam hB
  unfold sizeBound
  exact pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_right _ h)
end ExplicitCost
