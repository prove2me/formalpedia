-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.X_mem_opInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:45:49.338114+00:00
-- url     : https://prove2.me/submissions/83b66e6a-2060-41a2-a67b-1f6c774d7e29

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction

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
variable (K ι κ : Type) [NormedField K] [IsUltrametricDist K]
variable {K ι κ}
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (x : ι) : (MvPolynomial.X x : MvPolynomial ι K) ∈ Formalism.DworkPowerSeriesWeights.opInt K ι := by
  classical
  intro n
  rw [MvPolynomial.coeff_X]
  split_ifs <;> simp
end Formalism.InvariantFactorPaths.G7
