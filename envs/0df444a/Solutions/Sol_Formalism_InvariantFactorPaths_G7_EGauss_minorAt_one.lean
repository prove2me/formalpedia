-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.EGauss.minorAt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:00:11.483524+00:00
-- url     : https://prove2.me/submissions/ed920c50-3dbf-4392-ab5f-052bb77fac60

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
variable {K : Type} [Field K] {ν r0 r1 : ℕ}
namespace Formalism.InvariantFactorPaths.G7.EGauss
theorem _root_.solution {σ : Type} (s : σ) {l : ℕ} (h : l = 1) (T : Fin l → Fin r0 → K)
    (I : Fin l → Fin r1) :
    minorAt s T I = ∑ a, MvPolynomial.C (T ⟨0, by omega⟩ a) *
      MvPolynomial.X (s, a, I ⟨0, by omega⟩) := by
  subst h
  unfold minorAt
  rw [Matrix.det_fin_one]
  rfl
end Formalism.InvariantFactorPaths.G7.EGauss
