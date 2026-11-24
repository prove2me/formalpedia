-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.term_two_real_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:45:06.374413+00:00
-- url     : https://prove2.me/submissions/588e8a1f-6680-4d5d-9d5f-941c9c49da1c

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_Positivity
import Theorems.Thm_Formalism_ZeroFreeDirichlet_term_ofReal
import Theorems.Thm_Formalism_ZeroFreeDirichlet_vonMangoldt_div_rpow_nonneg
import Theorems.Thm_Formalism_ZeroFreeDirichlet_eq_one_or_eq_neg_one_of_sq_eq_one

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
theorem _root_.solution {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1) (σ : ℝ) (n : ℕ) :
    0 ≤ (term (↗(1 : DirichletCharacter ℂ q) * ↗Λ) (σ : ℂ) n).re
      + (term (↗χ₁ * ↗Λ) (σ : ℂ) n).re + (term (↗χ₂ * ↗Λ) (σ : ℂ) n).re
      + (term (↗(χ₁ * χ₂) * ↗Λ) (σ : ℂ) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_def]
  have ha := vonMangoldt_div_rpow_nonneg σ n
  rw [term_ofReal, term_ofReal, term_ofReal,
    term_ofReal, MulChar.mul_apply]
  by_cases hu : IsUnit (n : ZMod q)
  · rw [MulChar.one_apply hu]
    rcases eq_one_or_eq_neg_one_of_sq_eq_one χ₁ h₁ hu with h | h <;>
      rcases eq_one_or_eq_neg_one_of_sq_eq_one χ₂ h₂ hu with h' | h' <;> rw [h, h'] <;>
      generalize Λ n / (n : ℝ) ^ σ = a at ha ⊢ <;>
      simp [Complex.re_ofReal_mul] <;> linarith
  · rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu]
    simp
end Formalism.ZeroFreeDirichlet
