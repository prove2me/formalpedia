-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Eq.J.Neg.hensel_quad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:11:54.979786+00:00
-- url     : https://prove2.me/submissions/29d2231b-e50f-49ef-918b-177887da5126

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_SplitPairEquations_IntegralSquareRoots_HenselQuad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Formalism Formalism.L2 Formalism.L2.PairingIndexBounds Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq.J.Neg
namespace Formalism.L2.PairingIndexBounds.Eq.J.Neg
theorem _root_.solution (p : ℕ) [Fact p.Prime] (a b t : ℤ)
    (h : ‖((a * t ^ 2 + b : ℤ) : ℤ_[p])‖ < ‖((2 * a * t : ℤ) : ℤ_[p])‖ ^ 2) :
    ∃ z : ℤ_[p], (a : ℤ_[p]) * z ^ 2 + (b : ℤ_[p]) = 0 := by
  have h1 : aeval (t : ℤ_[p]) (C (a : ℤ_[p]) * X ^ 2 + C (b : ℤ_[p])) =
      ((a * t ^ 2 + b : ℤ) : ℤ_[p]) := by
    simp
  have h2 : aeval (t : ℤ_[p]) (derivative (C (a : ℤ_[p]) * X ^ 2 + C (b : ℤ_[p]))) =
      ((2 * a * t : ℤ) : ℤ_[p]) := by
    simp
    ring
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := C (a : ℤ_[p]) * X ^ 2 + C (b : ℤ_[p]))
    (a := (t : ℤ_[p])) (by rw [h1, h2]; exact h)
  exact ⟨z, by simpa using hz⟩
end Formalism.L2.PairingIndexBounds.Eq.J.Neg
