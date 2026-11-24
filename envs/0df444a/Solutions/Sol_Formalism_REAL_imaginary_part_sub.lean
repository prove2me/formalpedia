-- Prove2me | solution 1 for Formalism.REAL.imaginary_part_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:35:03.73589+00:00
-- url     : https://prove2.me/submissions/011ae30a-fbf0-4b88-9cee-5b6f8e2ca5a6

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    cpart2 ε (Z - W) = cpart2 ε Z - cpart2 ε W := by
  unfold cpart2
  rw [conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
  module
end Formalism.REAL
