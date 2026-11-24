-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ETerm.C_mul_monomial_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:54.556394+00:00
-- url     : https://prove2.me/submissions/00cf05b6-8f5f-4e18-90dc-fa6c221e107d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormNatCastLeOfDvd
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_right
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_eq_sum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_sum_right


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
open Formalism.InvariantFactorPaths.G7.ETerm
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact jetPair_eq_sum jetPair_C_mul_right jetPair_sum_right)
variable {K σ : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.ETerm
theorem _root_.solution (a : K) (d : σ →₀ ℕ) :
    MvPowerSeries.C a * MvPowerSeries.monomial d (1 : K) = MvPowerSeries.monomial d a := by
  rw [← MvPowerSeries.monomial_zero_eq_C_apply, MvPowerSeries.monomial_mul_monomial, zero_add,
    mul_one]
end Formalism.InvariantFactorPaths.G7.ETerm
