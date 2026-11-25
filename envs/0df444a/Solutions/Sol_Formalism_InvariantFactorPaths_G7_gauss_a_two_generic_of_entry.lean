-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.gauss_a_two_generic_of_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:13:19.820805+00:00
-- url     : https://prove2.me/submissions/f4620c5f-36d0-46ad-8cab-9051fa5bda5a

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementGK
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KernelFromKOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGaussK
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_EGaussK_reduce
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp frameJet jetPair minorProd)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open EGaussK DeterminantJetScaling ScaledSeriesSubstitution
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (hE : EntryCappedBound) : GaussBoundArbitraryGeneric := by
  intro K _ _ _ p _ ν r0 r1 _ u F TT colN hts hp I hp2 hn hu hF n
  obtain ⟨K', iK, hU, C, u', F', ξ, e, l, sf, T, I', hH, hb, hal, hcap, hls, -⟩ :=
    EGaussK.reduce K p ν r0 r1 u F TT colN hts hp I hp2 hn hu hF
  have h1 := hE K' p ν r0 r1 C u' F' TT ξ e l sf T I' hH
  rw [hal, hcap, hls] at h1
  exact (hb n).trans h1
end Formalism.InvariantFactorPaths.G7
