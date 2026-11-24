-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.EGauss.inClass_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:00:14.531966+00:00
-- url     : https://prove2.me/submissions/07cbde20-0ce6-464c-a22e-60f001a50130

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementG
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KOneConsequence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EGauss

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
variable {F K : Type} [NormedField F] [NormedField K] (φ : F →+* K) {ν r0 r1 : ℕ}
namespace Formalism.InvariantFactorPaths.G7.EGauss
theorem _root_.solution {ι : Type} (hφ : ∀ z, ‖φ z‖ = ‖z‖) (pp : F) (hh G : MvPowerSeries ι F)
    (h : InClass pp hh G) :
    InClass (φ pp) (MvPowerSeries.map φ hh) (MvPowerSeries.map φ G) := by
  obtain ⟨U, hU, hc⟩ := h
  refine ⟨fun i => MvPowerSeries.map φ (U i), fun i n => ?_, fun n => ?_⟩
  · rw [MvPowerSeries.coeff_map, hφ]
    exact hU i n
  · rw [MvPowerSeries.coeff_map, hc n, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_inv₀, map_pow, ← MvPowerSeries.coeff_map, map_mul, map_pow]
end Formalism.InvariantFactorPaths.G7.EGauss
