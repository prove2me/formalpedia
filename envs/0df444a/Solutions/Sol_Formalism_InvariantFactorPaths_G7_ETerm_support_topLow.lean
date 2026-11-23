-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.ETerm.support_topLow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:54:45.238078+00:00
-- url     : https://prove2.me/submissions/73b10b01-0e99-4819-a34b-391d7bb4cfdd

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
theorem _root_.solution [DecidableEq Tp] [DecidableEq Lw] (e : Tp →₀ ℕ) (R : MvPolynomial Lw K) :
    (topMonoP e * lowPoly R).support ⊆ R.support.image (jn e) := by
  intro m hm
  rw [MvPolynomial.mem_support_iff] at hm
  unfold topMonoP lowPoly at hm
  rw [MvPolynomial.coeff_monomial_mul'] at hm
  split_ifs at hm with hle
  · rw [one_mul] at hm
    by_contra hcon
    apply hm
    refine MvPolynomial.coeff_rename_eq_zero _ _ _ fun u hu => ?_
    by_contra hu0
    apply hcon
    rw [Finset.mem_image]
    refine ⟨u, MvPolynomial.mem_support_iff.2 hu0, ?_⟩
    unfold jn
    rw [hu]
    exact add_tsub_cancel_of_le hle
  · exact absurd rfl hm
end Formalism.InvariantFactorPaths.G7.ETerm
