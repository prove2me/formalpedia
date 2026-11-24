-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.aDil_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:51:39.310718+00:00
-- url     : https://prove2.me/submissions/e01905b8-b498-4716-a645-5e50ea35725b

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_dg_mul_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution (t : ℝ) (ht : t ≠ 0) : IsUnit (aDil k r t).det := by
  rw [aDil_eq, Matrix.det_diagonal]
  exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => left_ne_zero_of_mul_eq_one (dg_mul_inv k r t ht i))
end Formalism.FourierDecayAlt.P.B4
