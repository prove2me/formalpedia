-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution.scale_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:44:10.851088+00:00
-- url     : https://prove2.me/submissions/d8d3cb1b-0808-4a31-925c-040457f55795

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementJ
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EJoint
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLiftLeOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_OmegaOfTraceDuality
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EChain
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_MinorFormHomogeneity_coeff_subst_scale


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
theorem _root_.solution {K ι : Type} [Field K] {ϖ : K} (hϖ : ϖ ≠ 0) (f : MvPowerSeries ι K) :
    MvPowerSeries.subst (fun i => MvPowerSeries.C ϖ * (MvPowerSeries.X i : MvPowerSeries ι K))
      (MvPowerSeries.subst
        (fun i => MvPowerSeries.C ϖ⁻¹ * (MvPowerSeries.X i : MvPowerSeries ι K)) f) = f := by
  ext n
  rw [MinorFormHomogeneity.coeff_subst_scale, MinorFormHomogeneity.coeff_subst_scale, ← mul_assoc, ← mul_pow,
    mul_inv_cancel₀ hϖ, one_pow, one_mul]
end Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution
