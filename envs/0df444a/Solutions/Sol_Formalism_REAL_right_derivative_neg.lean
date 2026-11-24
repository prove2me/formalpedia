-- Prove2me | solution 1 for Formalism.REAL.right_derivative_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:35:48.294917+00:00
-- url     : https://prove2.me/submissions/f3c232c3-bcd8-45c4-8088-9c05a0ccbd07

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
theorem _root_.solution (hl : RdLin) {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {B g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnG ε f) (hB : inG ε B) (hg : inUJ ε g) :
    Rd (-B) f g = -Rd B f g := by
  have := (hl n ε f f B B (-1) 0 g hf hf hB hB hg).2.1
  have e : (((-1 : ℝ) : ℂ) • B) = -B := by simp
  rw [e] at this
  rw [this]; simp
end Formalism.REAL
