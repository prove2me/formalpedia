-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.jetPair_monomial_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:41.808115+00:00
-- url     : https://prove2.me/submissions/4b6d22e4-bedf-4e71-9c9a-1345fdc20435

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_eq_sum


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
variable {K ι : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (κ : ι →₀ ℕ) (a : K) (F : MvPowerSeries ι K) :
    jetPair (MvPolynomial.monomial κ a) F =
      a * ((Formalism.DworkPowerSeriesWeights.mfact κ : ℕ) : K) * MvPowerSeries.coeff κ F := by
  classical
  rw [Formalism.DworkPowerSeriesWeights.jetPair_eq_sum _ _ {κ} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]
end Formalism.InvariantFactorPaths.G7
