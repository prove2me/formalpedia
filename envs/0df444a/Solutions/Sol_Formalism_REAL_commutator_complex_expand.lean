-- Prove2me | solution 1 for Formalism.REAL.commutator_complex_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:58:29.710064+00:00
-- url     : https://prove2.me/submissions/3ed8931b-f2c5-4970-9571-60d9e40d08b4

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (X1 X2 Y1 Y2 : Matrix (Fin n) (Fin n) ℂ) :
    (X1 + Complex.I • X2) * (Y1 + Complex.I • Y2) - (Y1 + Complex.I • Y2) * (X1 + Complex.I • X2) =
      ((X1 * Y1 - Y1 * X1) - (X2 * Y2 - Y2 * X2)) +
        Complex.I • ((X1 * Y2 - Y2 * X1) + (X2 * Y1 - Y1 * X2)) := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul]
  match_scalars <;> first | ring1 | linear_combination Complex.I_sq | linear_combination -Complex.I_sq
end Formalism.REAL
