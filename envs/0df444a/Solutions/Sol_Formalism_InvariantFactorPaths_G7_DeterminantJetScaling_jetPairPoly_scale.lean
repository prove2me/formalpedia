-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DeterminantJetScaling.jetPairPoly_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:47.414539+00:00
-- url     : https://prove2.me/submissions/ce609d8a-1c52-4859-b1cb-697d200323f8

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EJoint
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EKernel
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_MinorFormHomogeneity_coeff_subst_scale


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
open Formalism.DworkPowerSeriesWeights (Integral frameJet jetPairPoly minorProd mfact)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7.DeterminantJetScaling
namespace Formalism.InvariantFactorPaths.G7.DeterminantJetScaling
theorem _root_.solution {K σ ι : Type} [Field K] (ϖ : K) (d : ℕ)
    (P : MvPolynomial ι (MvPolynomial σ K)) (hP : P.IsHomogeneous d) (Th : MvPowerSeries ι K) :
    jetPairPoly P (MvPowerSeries.subst
      (fun i => MvPowerSeries.C ϖ * (MvPowerSeries.X i : MvPowerSeries ι K)) Th) =
      MvPolynomial.C (ϖ ^ d) * jetPairPoly P Th := by
  unfold jetPairPoly
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun κ hκ => ?_
  have hd : κ.degree = d := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hκ) (hP.coeff_eq_zero hne)
  rw [MinorFormHomogeneity.coeff_subst_scale, hd, mul_left_comm (((mfact κ : ℕ) : K)), map_mul, mul_left_comm]
end Formalism.InvariantFactorPaths.G7.DeterminantJetScaling
