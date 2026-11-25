-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftDerivativeCurves.lcurve_hasDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:20:36.283235+00:00
-- url     : https://prove2.me/submissions/53520564-dd98-4494-922a-23580a018303

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_hasDerivAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.LeftDerivativeCurves
open Qx2 (Good)
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.LeftDerivativeCurves
theorem _root_.solution (X g : Mx k r) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * g) (X * g) 0 := by
  have h0 := Formalism.FourierDecayAlt.P.B5.curve_hasDerivAt (1 : Mx k r) X 0
  simp only [Matrix.one_mul, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at h0
  let R : Mx k r →L[ℝ] Mx k r := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ g)
  exact R.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h0
end Formalism.FourierDecayAlt.P.LeftDerivativeCurves
