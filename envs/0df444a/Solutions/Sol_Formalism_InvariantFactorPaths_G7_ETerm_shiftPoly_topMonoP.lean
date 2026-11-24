-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ETerm.shiftPoly_topMonoP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:06.373033+00:00
-- url     : https://prove2.me/submissions/60454516-942b-4621-a69a-359ac8d998ef

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
variable {K Tp Lw : Type} [Field K]
variable {κ : Type} [Fintype κ]
namespace Formalism.InvariantFactorPaths.G7.ETerm
theorem _root_.solution (b : κ → Lw → K) (e : Tp →₀ ℕ) :
    shiftPoly (ext0 (Tp := Tp) b) (topMonoP e) = MvPolynomial.C (topMonoP e) := by
  unfold shiftPoly topMonoP
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_mapDomain_index_inj Sum.inl_injective,
    MvPolynomial.monomial_eq, Finsupp.prod_mapDomain_index_inj Sum.inl_injective]
  simp [ext0, Finsupp.prod, map_prod]
end Formalism.InvariantFactorPaths.G7.ETerm
