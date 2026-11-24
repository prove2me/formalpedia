-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.degLE_det_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:22:08.328841+00:00
-- url     : https://prove2.me/submissions/856959e6-7428-49a1-8bb5-b106ea7eeb3e

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_det_col

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
variable {κ R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {l : ℕ} {W : Finset κ} (N : Matrix (Fin l) (Fin l) (MvPolynomial κ R))
    (n : Fin l → ℕ) (h : ∀ i c, degLE W (n i) (N i c)) : degLE W (∑ c, n c) N.det := by
  rw [← Matrix.det_transpose]
  exact degLE_det_col N.transpose n fun i c => h c i
end Formalism.InvariantFactorPaths.G7
