-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DeterminantJetScaling.det_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:47.326688+00:00
-- url     : https://prove2.me/submissions/bfa13a5f-8cc1-4251-aec8-f2d3d6141ca6

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EJoint
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EKernel
import Theorems.Thm_Formalism_FG_InvIntVAux_Low_sum
import Theorems.Thm_Formalism_LT_CoeffP_Bd_sum


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
theorem _root_.solution {R σ : Type} [CommRing R] {h : ℕ}
    (M : Matrix (Fin h) (Fin h) (MvPolynomial σ R)) (hM : ∀ i j, (M i j).IsHomogeneous 1) :
    M.det.IsHomogeneous h := by
  rw [Matrix.det_apply]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun π _ => ?_
  have hp : (∏ i : Fin h, M (π i) i).IsHomogeneous h := by
    have := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin h))
      (fun i => M (π i) i) (fun _ => 1) (fun i _ => hM _ _)
    simpa using this
  rw [Units.smul_def]
  exact (MvPolynomial.homogeneousSubmodule _ R h).toAddSubgroup.zsmul_mem hp _
end Formalism.InvariantFactorPaths.G7.DeterminantJetScaling
