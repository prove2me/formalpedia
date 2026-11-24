-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.EGauss.map_sPos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:11:19.27318+00:00
-- url     : https://prove2.me/submissions/e201cc2f-ffe4-4d7e-b7c1-7678f877e905

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
theorem _root_.solution (p : ℕ) (s : ZMod (2 * ν)) (ab : Fin r0 × Fin r1) :
    MvPowerSeries.map φ (sPos (K := F) p s ab) = sPos p s ab := by
  ext n
  rw [MvPowerSeries.coeff_map]
  change φ (∑ l ∈ range (n.degree + 1), _) = ∑ l ∈ range (n.degree + 1), _
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp
end Formalism.InvariantFactorPaths.G7.EGauss
