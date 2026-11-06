-- Prove2me | solution 1 for CountedInstance.thePairsMeetTheClauses
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:47:15.418905+00:00
-- url     : https://prove2.me/submissions/4d2642e6-87c4-4ec6-9512-66700e220cc5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedInstanceStatement
import Definitions.Def_CountedToPadded_GenLevels
import Definitions.Def_PairsToBound_Pairs
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_GeneralPieces_Num_Between
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_CountedInstance_Pairs
import Theorems.Thm_ClauseBound_Gen_Seq_two_le_K
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_QU_comp
import Theorems.Thm_ClauseBound_ParityChecks_CertOL_CU_comp
import Theorems.Thm_CliqueLevels_levelsAreComputed
import Theorems.Thm_GeneralPieces_Asymptotic_between
import Theorems.Thm_GeneralPieces_Between_between_half
import Theorems.Thm_GeneralPieces_Between_num_den_polyT
import Theorems.Thm_GeneralPieces_PartAUse_e_le_one
import Theorems.Thm_GeneralPieces_PartAUse_inv_logK_pow_le_e
import Theorems.Thm_GeneralPieces_PartAUse_two_le_K
import Theorems.Thm_GeneralPieces_PartA_thmRunningTime_a
import Theorems.Thm_GeneralPieces_thmRunningTime_a
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_PolyT_fst
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_Unary_comp
import Theorems.Thm_P2M_Groundwork_PB_id__8af0b594aff4
import Theorems.Thm_P2M_Groundwork_PolyT_id__1c5d0f44cc8f
import Theorems.Thm_PairsToBound_half_le_inv_sqrt_two
import Theorems.Thm_PairsToBound_thetaOfThePairs
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f



set_option autoImplicit false
section
section
open CountedInstance
open Groundwork
namespace CountedInstance
theorem _root_.solution : ThePairsMeetTheClauses := by
  intro x₀ C₀ hx hC
  obtain ⟨hρ, hρ1⟩ := PairsToBound.half_le_inv_sqrt_two
  have hA := GeneralPieces.PartA.thmRunningTime_a (1 / Real.sqrt 2) x₀ hρ hρ1 hx
  refine ⟨⟨by omega, fun l => GeneralPieces.PartAUse.two_le_K hA l, fun l => (hA.K_lt_le l).1,
    fun l => (hA.K_lt_le l).2.trans (Nat.pow_le_pow_right (by have := GeneralPieces.PartAUse.two_le_K hA l; omega) hC),
    fun l => GeneralPieces.PartAUse.inv_logK_pow_le_e hA hρ (by omega) l C₀ (by omega), fun l => GeneralPieces.PartAUse.e_le_one hA (by linarith) hρ1.le l⟩,
    CliqueLevels.levelsAreComputed x₀, ⟨?_, fun l => ?_⟩, fun l => ?_⟩
  · exact GeneralPieces.Between.num_den_polyT.comp (PolyT.fst PolyT.id')
  · have hb := GeneralPieces.Between.between_half l
    have h := GeneralPieces.Asymptotic.between (1 / Real.sqrt 2) x₀ l _ hρ hx hb.1 hb.2
    have e : (Printed.unary l).length = l := List.length_replicate
    change Levels.Gen.e (1 / Real.sqrt 2) x₀ l ≤ (GeneralPieces.Between.num (Printed.unary l).length : ℝ) / (GeneralPieces.Between.den (Printed.unary l).length : ℝ) ∧
      (GeneralPieces.Between.num (Printed.unary l).length : ℝ) / (GeneralPieces.Between.den (Printed.unary l).length : ℝ) ≤ 2 * Levels.Gen.e (1 / Real.sqrt 2) x₀ l
    rw [e]
    exact h
  · obtain ⟨-, -, -, -, -, h6⟩ := PairsToBound.thetaOfThePairs x₀ l hx
    have hx0 : (0 : ℝ) ≤ x₀ := Nat.cast_nonneg _
    have hs0 := Real.sqrt_nonneg (3 * (x₀ : ℝ) + 6)
    have hs : Real.sqrt (3 * (x₀ : ℝ) + 6) ≤ 3 * (x₀ : ℝ) + 6 := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    refine h6.trans (div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    push_cast
    linarith
end CountedInstance
