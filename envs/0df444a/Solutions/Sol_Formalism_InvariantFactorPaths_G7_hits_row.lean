-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.hits_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:56:41.694651+00:00
-- url     : https://prove2.me/submissions/2ba1a8cd-a64e-4c3f-8f86-e719c9735fb1

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_minor_row

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
open Formalism.DworkPowerSeriesWeights (jetPair)
variable {K σ κ : Type} [Field K] [DecidableEq σ] [Fintype κ]
variable {r0 r1 l : ℕ} (s : σ) (T : Fin l → Fin r0 → K) (I : Fin l → Fin r1) (pos : κ → σ)
  (ξ : κ → Fin r0 → K) (col : κ → Fin r1)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (W : Finset κ) (ξ0 : Fin r0 → K) (hW : ∀ k ∈ W, ξ k = ξ0) (β : κ →₀ ℕ)
    (hβ : 1 < ∑ k ∈ W, β k) :
    hasseDir (fun k => colDir (pos k) (ξ k) (col k)) β (minorAt s T I) = 0 := by
  by_contra h
  exact absurd (degLE_minor_row s T I pos ξ col W ξ0 hW β h) (not_le.mpr hβ)
end Formalism.InvariantFactorPaths.G7
