-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.hits_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:33:50.89197+00:00
-- url     : https://prove2.me/submissions/09e6614e-ed10-473f-9e3d-ef0e42e44b09

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_hasseDir_zero_right
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_minor_col

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
theorem _root_.solution (S : Finset κ) (J : Finset (Fin r1)) (hS : ∀ k ∈ S, pos k = s → col k ∈ J)
    (β : κ →₀ ℕ) (hβ : ((univ.image I) ∩ J).card < ∑ k ∈ S, β k) :
    hasseDir (fun k => colDir (pos k) (ξ k) (col k)) β (minorAt s T I) = 0 := by
  classical
  by_cases hI : Function.Injective I
  · by_contra h
    exact absurd (degLE_minor_col s T I pos ξ col hI S J hS β h) (not_le.mpr hβ)
  · have : minorAt s T I = 0 := by
      unfold Function.Injective at hI
      push Not at hI
      obtain ⟨c, c', hcc, hne⟩ := hI
      unfold minorAt
      refine Matrix.det_zero_of_column_eq hne fun i => ?_
      simp only [Matrix.of_apply, hcc]
    rw [this, hasseDir_zero_right]
end Formalism.InvariantFactorPaths.G7
