-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.cdo_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:46:34.559505+00:00
-- url     : https://prove2.me/submissions/c4d9fc56-ff37-4af1-b938-de30836383ee

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_cdo_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_cdo_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx3
theorem _root_.solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {f g : X → Mx k r} {s : Set X}
    (hf : ContDiffOn ℝ ∞ f s) (hg : ContDiffOn ℝ ∞ g s) : ContDiffOn ℝ ∞ (fun x => f x * g x) s := by
  refine cdo_matrix fun p q => ?_
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun x _ => (cdo_entry hf p x).mul (cdo_entry hg x q)
end Formalism.FourierDecayAlt.P.Qx3
