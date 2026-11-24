-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.C_mem_opInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:45:09.768851+00:00
-- url     : https://prove2.me/submissions/7b6738da-24d8-4c01-83a6-965c3404f958

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
theorem _root_.solution {c : K} (hc : ‖c‖ ≤ 1) :
    (MvPolynomial.C c : MvPolynomial ι K) ∈ Formalism.DworkPowerSeriesWeights.opInt K ι := by
  classical
  intro n
  rw [MvPolynomial.coeff_C]
  split_ifs
  · exact hc
  · simp
end Formalism.InvariantFactorPaths.G7
