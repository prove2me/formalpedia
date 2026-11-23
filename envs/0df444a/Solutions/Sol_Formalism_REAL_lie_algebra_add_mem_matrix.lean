-- Prove2me | solution 1 for Formalism.REAL.lie_algebra_add_mem_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:51:42.217072+00:00
-- url     : https://prove2.me/submissions/e437328a-c3a6-4bdc-ac3e-1b883c09bdee

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
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : inG ε A) (hB : inG ε B) : inG ε (A + B) := by
  unfold inG at *
  rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
  calc Aᴴ * Jm ε + Bᴴ * Jm ε + (Jm ε * A + Jm ε * B)
      = (Aᴴ * Jm ε + Jm ε * A) + (Bᴴ * Jm ε + Jm ε * B) := by abel
    _ = 0 := by rw [hA, hB, add_zero]
end Formalism.REAL
