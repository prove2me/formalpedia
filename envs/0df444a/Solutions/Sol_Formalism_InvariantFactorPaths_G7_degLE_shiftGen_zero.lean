-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.degLE_shiftGen_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:10:39.288804+00:00
-- url     : https://prove2.me/submissions/4702bef7-0061-48c7-b953-a6bdf4031032

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_X_of_notMem
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_CC

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
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {ι : Type} (W : Finset κ) (b : κ → ι → K) (x : ι)
    (h : ∀ k ∈ W, b k x = 0) : degLE W 0 (shiftGen b x) := by
  unfold shiftGen
  refine degLE_add (degLE_C W _) (degLE_sum _ _ fun k _ => ?_)
  by_cases hk : k ∈ W
  · rw [h k hk]
    simpa using degLE_zero W 0
  · simpa using degLE_mul (degLE_CC W (b k x)) (degLE_X_of_notMem hk)
end Formalism.InvariantFactorPaths.G7
