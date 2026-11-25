-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.theta_log_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:12:19.474306+00:00
-- url     : https://prove2.me/submissions/0fbc37f1-408c-4f19-933e-63db8128e13e

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementJ
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EJoint
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLiftLeOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_OmegaOfTraceDuality
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EChain
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ScaledSeriesSubstitution_hasSubst_scale
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ScaledSeriesSubstitution_subst_C_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ScaledSeriesSubstitution_constantCoeff_zLin
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ScaledSeriesSubstitution_subst_scale_zLin
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ScaledSeriesSubstitution_ps_subst_C_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_subst_subst
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_subst_subst
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_constantCoeff_zLin
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_log_coordinates


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
open ScaledSeriesSubstitution
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : ThetaLogCoord := by
  intro K _ p ν r0 r1 _ om oms ϖ μ x hp hpK hϖ hμ0 hμ
  have hb := hasSubst_scale (K := K) (ι := ZV ν r0 r1) ϖ⁻¹
  have hz : PowerSeries.HasSubst (zLin om oms x : MvPowerSeries (ZV ν r0 r1) K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_zLin om oms x)
  have hw : PowerSeries.HasSubst
      (MvPowerSeries.C ϖ⁻¹ * zLin om oms x : MvPowerSeries (ZV ν r0 r1) K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by rw [map_mul, constantCoeff_zLin, mul_zero])
  have hm : PowerSeries.HasSubst (PowerSeries.C ϖ * μ : PowerSeries K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by rw [map_mul, hμ0, mul_zero])
  have e1 : MvPowerSeries.subst
      (fun y => MvPowerSeries.C ϖ⁻¹ * (MvPowerSeries.X y : MvPowerSeries (ZV ν r0 r1) K))
      (MvPowerSeries.C ϖ * sSub om oms μ x) =
      PowerSeries.subst (MvPowerSeries.C ϖ⁻¹ * zLin om oms x) (PowerSeries.C ϖ * μ) := by
    rw [subst_C_mul hb, ps_subst_C_mul hw]
    unfold sSub
    rw [FormalGroupLaws.subst_subst hb hz, subst_scale_zLin]
  have e2 := congrArg (fun f => (PowerSeries.subst (MvPowerSeries.C ϖ⁻¹ * zLin om oms x) f :
    MvPowerSeries (ZV ν r0 r1) K)) (log_coordinates K p ϖ μ hp hpK hμ0 hμ)
  rw [PowerSeries.subst_comp_subst_apply hm hw, ps_subst_C_mul hw ϖ PowerSeries.X,
    PowerSeries.subst_X hw,
    ← mul_assoc, ← map_mul, mul_inv_cancel₀ hϖ, map_one, one_mul] at e2
  rw [e1]
  exact e2
end Formalism.InvariantFactorPaths.G7
