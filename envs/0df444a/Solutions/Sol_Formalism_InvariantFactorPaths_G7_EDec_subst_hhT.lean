-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.EDec.subst_hhT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:45:12.580803+00:00
-- url     : https://prove2.me/submissions/cc051b58-fa82-4e6c-97a6-f1bd635c2b2c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EDecomp
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EDec_constantCoeff_zSub
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
theorem _root_.solution [NeZero ν] (TT : Finset (ZMod (2 * ν))) (ξ : ZMod (2 * ν) → Fin r0 → K) (p E : ℕ)
    (u : ZMod (2 * ν) → K) :
    MvPowerSeries.subst (zSub TT ξ) (hhT (r0 := r0) (r1 := r1) p E u) =
      ∑ s : ZMod (2 * ν), MvPowerSeries.C (u s) * ∑ ab : Fin r0 × Fin r1,
        MvPowerSeries.subst (zSub TT ξ) (sT (K := K) p E s ab) ^ p *
          MvPowerSeries.subst (zSub TT ξ) (sT (K := K) p E (s + 1) ab) := by
  have hs : MvPowerSeries.HasSubst (zSub (r1 := r1) TT ξ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_zSub TT ξ)
  have hC : ∀ r : K, MvPowerSeries.substAlgHom hs (MvPowerSeries.C r) = MvPowerSeries.C r :=
    fun r => (MvPowerSeries.substAlgHom hs).commutes r
  rw [← MvPowerSeries.coe_substAlgHom hs, hhT, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, hC, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [map_mul, map_pow]
end Formalism.InvariantFactorPaths.G7.EDec
