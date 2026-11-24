-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution.subst_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:44:11.684187+00:00
-- url     : https://prove2.me/submissions/8f1352ed-9f69-412c-96bf-e8453778c321

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
theorem _root_.solution {K ι κ : Type} [Field K] {b : ι → MvPowerSeries κ K}
    (hb : MvPowerSeries.HasSubst b) (a : K) (f : MvPowerSeries ι K) :
    MvPowerSeries.subst b (MvPowerSeries.C a * f) = MvPowerSeries.C a * MvPowerSeries.subst b f := by
  rw [← MvPowerSeries.smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul, MvPowerSeries.subst_smul hb]
end Formalism.InvariantFactorPaths.G7.ScaledSeriesSubstitution
