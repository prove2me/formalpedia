-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.EDec.A_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:00:50.960039+00:00
-- url     : https://prove2.me/submissions/fa4407a7-ab65-4ff2-94c6-18c5785f1eda

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EDecomp
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_topMonoS_single
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_topMonoS_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_tpS_pos
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_tpS_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_aAof_pos
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_aAof_neg
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_of_zero
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_frob_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_frob_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_of_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_refl
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_symm
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_trans
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_coeff_sPos
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_pinv_nonneg


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
open Formalism.DworkPowerSeriesWeights (Integral low_subst_of_low)
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_mul low_pow low_one_iff low_mul_sub
  low_of_zero)
open Formalism.FG.IntegralSubstitution (integral_mul integral_pow integral_one)
open TwoS (Cg cg_refl cg_of_eq cg_symm cg_trans cg_add cg_sum cg_mul cg_pow cg_frob_add cg_frob_sum
  integral_add integral_neg integral_sum integral_C integral_X integral_zero coeff_sPos pinv_nonneg)
open Formalism.InvariantFactorPaths.G7.EDec
variable {K : Type} [Field K] {ν r0 r1 : ℕ}
namespace Formalism.InvariantFactorPaths.G7.EDec
theorem _root_.solution {E : ℕ} {p : ℕ} (hp : p ≠ 0) (u : ZMod (2 * ν) → K) (TT : Finset (ZMod (2 * ν)))
    (ξ : ZMod (2 * ν) → Fin r0 → K) (s : ZMod (2 * ν)) (l l' : Fin E) (ab : Fin r0 × Fin r1) :
    MvPowerSeries.C (u s) *
        (((-1) ^ l.val * tpS TT ξ (s - 2 * (l.val : ZMod (2 * ν)), ab) ^ (p ^ (1 + 2 * l.val))) *
          ((-1) ^ l'.val * tpS TT ξ (s + 1 - 2 * (l'.val : ZMod (2 * ν)), ab) ^ (p ^ (2 * l'.val)))) =
      MvPowerSeries.C (aAof p u TT ξ (s, l, l', ab)) *
        topMonoS (Lw := ZV ν r0 r1) (dAof p (s, l, l', ab)) := by
  have n1 : p ^ (1 + 2 * l.val) ≠ 0 := pow_ne_zero _ hp
  have n2 : p ^ (2 * l'.val) ≠ 0 := pow_ne_zero _ hp
  by_cases h1 : s - 2 * (l.val : ZMod (2 * ν)) ∈ TT
  · by_cases h2 : s + 1 - 2 * (l'.val : ZMod (2 * ν)) ∈ TT
    · rw [tpS_pos (x := (s - 2 * (l.val : ZMod (2 * ν)), ab)) ξ h1,
        tpS_pos (x := (s + 1 - 2 * (l'.val : ZMod (2 * ν)), ab)) ξ h2,
        aAof_pos (φ := (s, l, l', ab)) p u ξ ⟨h1, h2⟩, dAof, topMonoS_add, topMonoS_single,
        topMonoS_single]
      simp only [pairFirst, pairSecond, map_mul, map_pow, map_neg, map_one, mul_pow]
      ring
    · rw [tpS_neg (x := (s + 1 - 2 * (l'.val : ZMod (2 * ν)), ab)) ξ h2,
        aAof_neg (φ := (s, l, l', ab)) p u ξ (fun h => h2 h.2), zero_pow n2]
      simp
  · rw [tpS_neg (x := (s - 2 * (l.val : ZMod (2 * ν)), ab)) ξ h1,
      aAof_neg (φ := (s, l, l', ab)) p u ξ (fun h => h1 h.1), zero_pow n1]
    simp
end Formalism.InvariantFactorPaths.G7.EDec
