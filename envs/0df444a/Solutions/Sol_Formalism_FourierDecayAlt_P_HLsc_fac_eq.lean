-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HLsc.fac_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:51:52.809528+00:00
-- url     : https://prove2.me/submissions/852d787d-da54-4118-878c-f80a3a79dd23

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HLsc
open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.HLsc
theorem _root_.solution (t : ℝ) : ‖1 + Complex.exp (2 * π * Complex.I * (t : ℂ))‖ ^ 2 = 2 + 2 * Real.cos (2 * π * t) := by
  have h : (2 * π * Complex.I * (t : ℂ)) = ((2 * π * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_mul_I, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]
  simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.one_im, Complex.mul_im]
  nlinarith [Real.sin_sq_add_cos_sq (2 * π * t)]
end Formalism.FourierDecayAlt.P.HLsc
