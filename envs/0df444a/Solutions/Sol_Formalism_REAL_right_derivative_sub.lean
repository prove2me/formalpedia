-- Prove2me | solution 1 for Formalism.REAL.right_derivative_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:44:05.124257+00:00
-- url     : https://prove2.me/submissions/e4f7e08d-162c-4b0a-b1f0-6230f189c555

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Theorems.Thm_Formalism_REAL_lie_algebra_neg_mem
import Theorems.Thm_Formalism_REAL_right_derivative_neg
import Theorems.Thm_Formalism_REAL_right_derivative_add

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
theorem _root_.solution (hl : RdLin) {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {A B g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnG ε f) (hA : inG ε A) (hB : inG ε B)
    (hg : inUJ ε g) : Rd (A - B) f g = Rd A f g - Rd B f g := by
  rw [sub_eq_add_neg, right_derivative_add hl hf hA (lie_algebra_neg_mem hB) hg, right_derivative_neg hl hf hB hg, sub_eq_add_neg]
end Formalism.REAL
