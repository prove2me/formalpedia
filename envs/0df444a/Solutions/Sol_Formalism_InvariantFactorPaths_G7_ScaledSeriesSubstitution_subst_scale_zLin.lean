-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution.subst_scale_zLin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:05:21.04497+00:00
-- url     : https://prove2.me/submissions/9b3654ed-ec0f-4366-be32-6a6f72046d5e

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementJ
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EJoint
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLiftLeOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_OmegaOfTraceDuality
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EChain
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ScaledSeriesSubstitution_hasSubst_scale
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ScaledSeriesSubstitution_subst_C_mul

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp frameJet)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution
namespace Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution
theorem _root_.solution {K : Type} [Field K] {ν r0 r1 : ℕ} [NeZero ν]
    (om oms : Fin ν → ZMod (2 * ν) → K) (a : K) (x : Bool × EV ν r0 r1) :
    MvPowerSeries.subst
        (fun y => MvPowerSeries.C a * (MvPowerSeries.X y : MvPowerSeries (ZV ν r0 r1) K))
        (zLin om oms x) = MvPowerSeries.C a * zLin om oms x := by
  have hb := hasSubst_scale (K := K) (ι := ZV ν r0 r1) a
  unfold zLin
  rw [← MvPowerSeries.coe_substAlgHom hb, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MvPowerSeries.coe_substAlgHom hb]
  split_ifs
  · rw [subst_C_mul hb, MvPowerSeries.subst_X hb, mul_left_comm]
  · rw [← MvPowerSeries.coe_substAlgHom hb, map_zero, mul_zero]
  · rw [subst_C_mul hb, MvPowerSeries.subst_X hb, mul_left_comm]
  · rw [← MvPowerSeries.coe_substAlgHom hb, map_zero, mul_zero]
end Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution
