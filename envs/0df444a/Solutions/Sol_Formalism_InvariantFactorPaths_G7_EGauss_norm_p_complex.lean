-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.EGauss.norm_p_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:00:15.178415+00:00
-- url     : https://prove2.me/submissions/95143a33-0a5d-477c-b550-0901c58320c6

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementG
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KOneConsequence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGauss
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_intCast_padicComplex


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
open Formalism.DworkPowerSeriesWeights (Integral frameJet jetPair minorProd)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.EGauss
namespace Formalism.InvariantFactorPaths.G7.EGauss
theorem _root_.solution (p : ℕ) [Fact p.Prime] : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  have h := Formalism.DworkPowerSeriesWeights.norm_intCast_padicComplex p (p : ℤ)
  rw [Int.cast_natCast, Int.cast_natCast] at h
  rw [h]
  exact Padic.norm_p
end Formalism.InvariantFactorPaths.G7.EGauss
