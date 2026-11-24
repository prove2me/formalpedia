-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.gauss_a_one_of_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:15:57.833155+00:00
-- url     : https://prove2.me/submissions/06255ae7-0427-4b64-b57b-fb149cd71164

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementG
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KOneConsequence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGauss
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EGauss_reduce

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
open EGauss
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (hE : EntryExcessBound) : FrameJetExcessBound := by
  intro p _ ν r0 r1 _ u F TT colN hts hp I hp2 hu hF n
  obtain ⟨K, instK, hult, C, u', F', ξ, e, l, sf, T, I', hyp, hco, hal, hcap, hls, -⟩ :=
    reduce p ν r0 r1 u F TT colN hts hp I hp2 hu hF
  have h := hE K p ν r0 r1 C u' F' TT ξ e l sf T I' hyp
  rw [hal, hcap, hls] at h
  exact (hco n).trans h
end Formalism.InvariantFactorPaths.G7
