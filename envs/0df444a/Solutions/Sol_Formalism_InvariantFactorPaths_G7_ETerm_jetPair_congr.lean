-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ETerm.jetPair_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:56.702417+00:00
-- url     : https://prove2.me/submissions/f19cc034-ac59-4d49-a017-362807e9cbc3

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
namespace Formalism.InvariantFactorPaths.G7.ETerm
theorem _root_.solution {ι : Type} (P : MvPolynomial ι K) (G G' : MvPowerSeries ι K)
    (h : ∀ m ∈ P.support, MvPowerSeries.coeff m G = MvPowerSeries.coeff m G') :
    jetPair P G = jetPair P G' := by
  unfold jetPair
  exact Finset.sum_congr rfl fun m hm => by rw [h m hm]
end Formalism.InvariantFactorPaths.G7.ETerm
