-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.dwork_multivariable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:10:14.641089+00:00
-- url     : https://prove2.me/submissions/6d657db7-1221-4751-8f2f-ef434e0877e0

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_of_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_constantCoeff_mvExp
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_exp_small
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_small_of_exp
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_of_frob
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_mvExp_natMul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_mvExp
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_neg
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_mvExp_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_neg low_mul low_pow low_one_iff)
open DworkIntegrality
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : DworkMv := by
  intro K ι _ _ _ _ p σ hp hnp hσ Ψ h0
  have hpos : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  rw [← PhiH_apply hp.ne_zero]
  have hΦ0 : MvPowerSeries.constantCoeff (PhiH hp.ne_zero σ Ψ) = 0 := by
    rw [PhiH_apply, frobVar_eq_expand hp.ne_zero, MvPowerSeries.constantCoeff_expand,
      MvPowerSeries.constantCoeff_map, h0, map_zero]
  have hpΨ0 : MvPowerSeries.constantCoeff (MvPowerSeries.C (p : K) * Ψ) = 0 := by simp [h0]
  have hDe0 : MvPowerSeries.constantCoeff (PhiH hp.ne_zero σ Ψ - MvPowerSeries.C (p : K) * Ψ) = 0 := by
    rw [map_sub, hΦ0, hpΨ0, sub_zero]
  have hpow : mvExp (MvPowerSeries.C (p : K) * Ψ) = (mvExp Ψ) ^ p := by
    obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.pos; omega⟩
    exact mvExp_natMul h0 n
  have hid : PhiH hp.ne_zero σ (mvExp Ψ) =
      (mvExp Ψ) ^ p * mvExp (PhiH hp.ne_zero σ Ψ - MvPowerSeries.C (p : K) * Ψ) := by
    rw [PhiH_mvExp hp.ne_zero σ h0, ← hpow, ← mvExp_add hpΨ0 hDe0]
    congr 1
    ring
  have hF1 := constantCoeff_mvExp h0
  have hG1 := constantCoeff_mvExp hDe0
  constructor
  · intro hint
    have hB := frob_congr hp hnp hσ (f := mvExp Ψ) hint
    refine small_of_exp hp hnp hDe0 (bd_of_mul hpos (U := (mvExp Ψ) ^ p) (int_pow hint p)
      (by rw [map_pow, hF1, one_pow]) ?_)
    have e : (mvExp (PhiH hp.ne_zero σ Ψ - MvPowerSeries.C (p : K) * Ψ) - 1) * (mvExp Ψ) ^ p =
        -((mvExp Ψ) ^ p - PhiH hp.ne_zero σ (mvExp Ψ)) := by
      rw [hid]; ring
    rw [e]
    exact bd_neg hB
  · intro hsm
    exact int_of_frob hp hnp hσ hF1 hG1 (exp_small hp hnp hDe0 hsm) hid
end Formalism.InvariantFactorPaths.G7
