-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ETerm.jn_inl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:47.333046+00:00
-- url     : https://prove2.me/submissions/d8e73cbc-25e4-4119-b22a-d2e649cb133b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormNatCastLeOfDvd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_mapDomain_inl_inl
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_mapDomain_inr_inl
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
variable {Tp Lw : Type}
namespace Formalism.InvariantFactorPaths.G7.ETerm
theorem _root_.solution (e : Tp →₀ ℕ) (n : Lw →₀ ℕ) (τ : Tp) : jn e n (Sum.inl τ) = e τ := by
  simp [jn, mapDomain_inl_inl, mapDomain_inr_inl]
end Formalism.InvariantFactorPaths.G7.ETerm
