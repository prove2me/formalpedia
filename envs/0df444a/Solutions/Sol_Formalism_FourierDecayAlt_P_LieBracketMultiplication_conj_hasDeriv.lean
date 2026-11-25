-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LieBracketMultiplication.conj_hasDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:29:46.152679+00:00
-- url     : https://prove2.me/submissions/767b2255-1b22-436f-992b-161fa04348de

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieBracketMultiplication
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_lcurve_hasDeriv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_REAL_hasDerivAt_mul_exp_smul_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.LieBracketMultiplication
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.LieBracketMultiplication
theorem _root_.solution (X Y : Mx k r) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • X) * Y * NormedSpace.exp ((s : ℂ) • (-X)))
      (X * Y - Y * X) 0 := by
  have hu := LeftDerivativeCurves.lcurve_hasDeriv X Y
  have hv := hasDerivAt_mul_exp_smul_zero (1 : Mx k r) (-X)
  have h : HasDerivAt
      (fun s : ℝ => NormedSpace.exp ((s : ℂ) • X) * Y * ((1 : Mx k r) * NormedSpace.exp ((s : ℂ) • (-X))))
      (NormedSpace.exp (((0 : ℝ) : ℂ) • X) * Y * ((1 : Mx k r) * -X) +
        X * Y * ((1 : Mx k r) * NormedSpace.exp (((0 : ℝ) : ℂ) • (-X)))) 0 :=
    (mulB k r).hasDerivAt_of_bilinear (fun _ => hu) (fun _ => hv)
  simp only [Matrix.one_mul, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one,
    Matrix.mul_neg] at h
  rw [neg_add_eq_sub] at h
  exact h
end Formalism.FourierDecayAlt.P.LieBracketMultiplication
