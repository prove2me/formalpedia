-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.biHom_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:45:54.891009+00:00
-- url     : https://prove2.me/submissions/2e83da10-5338-495e-ba82-bf12ca6d79ea

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biHom_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_biHom_one

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
variable {K ι κ : Type} [Field K] [Fintype κ]
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {d : ℕ} {F : MvPolynomial κ (MvPolynomial ι K)} (hF : biHom d F) (m : ℕ) :
    biHom (m * d) (F ^ m) := by
  induction m with
  | zero => simpa using biHom_one
  | succ m ih =>
    rw [pow_succ, Nat.succ_mul]
    exact biHom_mul ih hF
end Formalism.InvariantFactorPaths.G7
