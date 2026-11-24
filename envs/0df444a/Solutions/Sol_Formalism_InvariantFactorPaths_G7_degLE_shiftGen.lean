-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.degLE_shiftGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:10:38.441014+00:00
-- url     : https://prove2.me/submissions/aece810e-a3c4-414f-ae60-c824cb21e90c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_mono
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_X
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
theorem _root_.solution {ι : Type} (W : Finset κ) (b : κ → ι → K) (x : ι) :
    degLE W 1 (shiftGen b x) := by
  unfold shiftGen
  refine degLE_add (degLE_mono (degLE_C W _) (Nat.zero_le _)) (degLE_sum _ _ fun k _ => ?_)
  simpa using degLE_mul (degLE_CC W (b k x)) (degLE_X W k)
end Formalism.InvariantFactorPaths.G7
