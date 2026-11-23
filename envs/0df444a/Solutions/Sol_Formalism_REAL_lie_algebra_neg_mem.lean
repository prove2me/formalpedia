-- Prove2me | solution 1 for Formalism.REAL.lie_algebra_neg_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:04.973353+00:00
-- url     : https://prove2.me/submissions/9be58624-960d-452f-9576-90a25aa9d1be

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
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : inG ε A) : inG ε (-A) := by
  unfold inG at *
  rw [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hA, neg_zero]
end Formalism.REAL
