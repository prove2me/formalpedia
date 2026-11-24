-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ETerm.jetPair_topLow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:45:17.129695+00:00
-- url     : https://prove2.me/submissions/6520ce4b-0e94-4724-ab16-2480892a68d1

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormNatCastLeOfDvd
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_jn_injective
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_mfact_jn
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_coeff_jn
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_support_topLow
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
theorem _root_.solution [Fintype Tp] [Fintype Lw] (e : Tp →₀ ℕ)
    (R : MvPolynomial Lw K) (G : MvPowerSeries (Tp ⊕ Lw) K) :
    jetPair (topMonoP e * lowPoly R) G =
      ∑ n ∈ R.support, MvPolynomial.coeff n R * ((mfact e * mfact n : ℕ) : K) *
        MvPowerSeries.coeff (jn e n) G := by
  classical
  rw [jetPair_eq_sum _ _ _ (support_topLow e R), Finset.sum_image (fun a _ c _ h => jn_injective e h)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [coeff_jn, mfact_jn]
end Formalism.InvariantFactorPaths.G7.ETerm
