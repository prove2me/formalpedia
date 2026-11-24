-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.term_ofReal_add_mul_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:44:56.139645+00:00
-- url     : https://prove2.me/submissions/24c24d82-b254-4301-a300-63a65055d588

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
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ u : ℝ) (n : ℕ) :
    term (↗χ * ↗Λ) ((σ : ℂ) + u * I) n =
      ((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ) * (χ n / (n : ℂ) ^ ((u : ℂ) * I)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_def]
  · have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [LSeries.term_def, if_neg hn, Complex.cpow_add _ _ hn']
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    simp only [Pi.mul_apply]
    rw [div_mul_div_comm]
    ring
end Formalism.ZeroFreeDirichlet
