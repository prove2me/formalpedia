-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoS.subst_exp_Gtot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:38.850072+00:00
-- url     : https://prove2.me/submissions/88e9185d-469c-4a54-b9a4-6c0190039ca5

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_subst_mvExp
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_constantCoeff_Gtot
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_subst_Gtot
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_finsum_le_of
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp low_subst_of_low norm_finsum_le_of)
open Formalism.FG.SolveVAux (Low low_pow low_one_iff)
open Formalism.FG.IntegralSubstitution (integral_mul integral_pow integral_one integralSubstV)
open TwoS
open Formalism.InvariantFactorPaths.G7.TwoS
namespace Formalism.InvariantFactorPaths.G7.TwoS
theorem _root_.solution {K E : Type} [NormedField K] [CharZero K] [Fintype E] {p : ℕ} (hp : p ≠ 0)
    (c c' ϖ : K) :
    MvPowerSeries.subst (fun x : Bool × E => MvPowerSeries.C ϖ *
        (MvPowerSeries.X x : MvPowerSeries (Bool × E) K)) (mvExp (-(Gtot (E := E) p c c' 1))) =
      mvExp (-(Gtot p c c' ϖ)) := by
  have hψ : MvPowerSeries.HasSubst (fun x : Bool × E => MvPowerSeries.C ϖ *
      (MvPowerSeries.X x : MvPowerSeries (Bool × E) K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun x => by simp
  rw [subst_mvExp hψ (by rw [map_neg, constantCoeff_Gtot hp, neg_zero]),
    ← MvPowerSeries.coe_substAlgHom hψ, map_neg, MvPowerSeries.coe_substAlgHom hψ, subst_Gtot]
end Formalism.InvariantFactorPaths.G7.TwoS
