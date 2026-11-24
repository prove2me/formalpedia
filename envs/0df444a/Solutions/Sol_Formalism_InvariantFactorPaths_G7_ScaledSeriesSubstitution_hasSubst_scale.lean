-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution.hasSubst_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:44:22.163777+00:00
-- url     : https://prove2.me/submissions/f6a23ece-c782-43e6-bce4-d5c09b6216ae

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementJ
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EJoint
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLiftLeOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_OmegaOfTraceDuality
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EChain

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
theorem _root_.solution {K ι : Type} [Field K] [Finite ι] (a : K) :
    MvPowerSeries.HasSubst
      (fun i => MvPowerSeries.C a * (MvPowerSeries.X i : MvPowerSeries ι K)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by simp
end Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution
