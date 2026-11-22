-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.term_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:29.059113+00:00
-- url     : https://prove2.me/submissions/945d12a3-6a44-44bf-b7d3-0eabc964f081

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_Positivity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ : ℝ) (n : ℕ) :
    term (↗χ * ↗Λ) (σ : ℂ) n = ((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ) * χ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_def]
  · rw [LSeries.term_def, if_neg hn]
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    simp only [Pi.mul_apply]
    ring
end Formalism.ZeroFreeDirichlet
