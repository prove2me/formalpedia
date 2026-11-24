-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoS.subst_Gtot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:59.851867+00:00
-- url     : https://prove2.me/submissions/6ceba1b3-3403-4faf-b844-f32e20f30f4a

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
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
theorem _root_.solution {K E : Type} [Field K] [Fintype E] (p : ℕ) (c c' ϖ : K) :
    MvPowerSeries.subst (fun x : Bool × E => MvPowerSeries.C ϖ *
        (MvPowerSeries.X x : MvPowerSeries (Bool × E) K)) (Gtot (E := E) p c c' 1) =
      Gtot p c c' ϖ := by
  have hψ : MvPowerSeries.HasSubst (fun x : Bool × E => MvPowerSeries.C ϖ *
      (MvPowerSeries.X x : MvPowerSeries (Bool × E) K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun x => by simp
  unfold Gtot
  rw [← MvPowerSeries.coe_substAlgHom hψ, map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPowerSeries.coe_substAlgHom hψ, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun a => by simp) hψ]
  congr 1
  funext a
  rw [map_one, one_mul, MvPowerSeries.subst_X hψ]
end Formalism.InvariantFactorPaths.G7.TwoS
