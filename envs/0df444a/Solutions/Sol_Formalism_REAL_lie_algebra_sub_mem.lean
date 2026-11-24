-- Prove2me | solution 1 for Formalism.REAL.lie_algebra_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:35:00.543888+00:00
-- url     : https://prove2.me/submissions/7c88b9eb-2c5a-49a8-ba35-8b7173064d20

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Theorems.Thm_Formalism_REAL_lie_algebra_add_mem_matrix
import Theorems.Thm_Formalism_REAL_lie_algebra_neg_mem

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
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : inG ε A) (hB : inG ε B) : inG ε (A - B) := by
  rw [sub_eq_add_neg]; exact lie_algebra_add_mem_matrix hA (lie_algebra_neg_mem hB)
end Formalism.REAL
