-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DeterminantJetScaling.minorProd_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:45:12.337826+00:00
-- url     : https://prove2.me/submissions/dac328a9-31dd-455a-8d3d-dac90e9c35a9

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EJoint
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EKernel
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DeterminantJetScaling_det_hom

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
theorem _root_.solution {R σ : Type} [CommRing R] {N0 N1 C : ℕ}
    (row : Fin N0 → Fin N1 → MvPolynomial σ R) (hrow : ∀ i b, (row i b).IsHomogeneous 1)
    (q : Fin C → ℕ) (hq : ∀ c, q c ≤ N0) (I : ∀ c, Fin (q c) → Fin N1) :
    (minorProd row q hq I).IsHomogeneous (∑ c, q c) := by
  unfold minorProd
  refine MvPolynomial.IsHomogeneous.prod _ _ _ fun c _ => ?_
  refine det_hom _ fun i j => ?_
  rw [Matrix.of_apply]
  exact hrow _ _
end Formalism.InvariantFactorPaths.G7.DeterminantJetScaling
