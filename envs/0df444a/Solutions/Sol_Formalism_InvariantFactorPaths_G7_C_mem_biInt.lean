-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.C_mem_biInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:45:07.943+00:00
-- url     : https://prove2.me/submissions/4b5aaf16-2bf6-4cad-a5a5-6441e8e5fb83

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
theorem _root_.solution {p : MvPolynomial ι K} (hp : p ∈ Formalism.DworkPowerSeriesWeights.opInt K ι) :
    (MvPolynomial.C p : MvPolynomial κ (MvPolynomial ι K)) ∈ biInt K ι κ := by
  classical
  intro β
  rw [MvPolynomial.coeff_C]
  split_ifs
  · exact hp
  · exact Subring.zero_mem _
end Formalism.InvariantFactorPaths.G7
