-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.negLogDerivPositivity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:13:32.448428+00:00
-- url     : https://prove2.me/submissions/adfd2c8f-ab40-4944-bc28-f201519c2b2b

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_Positivity
import Theorems.Thm_Formalism_ZeroFreeDirichlet_hasSum_re_term
import Theorems.Thm_Formalism_ZeroFreeDirichlet_term_three_four_one_nonneg
import Theorems.Thm_Formalism_ZeroFreeDirichlet_term_one_add_real_nonneg
import Theorems.Thm_Formalism_ZeroFreeDirichlet_term_two_real_nonneg

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
theorem _root_.solution : Positivity := by
  intro q _ σ hσ
  have hs1 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have H1 : ∀ χ : DirichletCharacter ℂ q, HasSum (fun n ↦ (term (↗χ * ↗Λ) (σ : ℂ) n).re)
      (negLD χ (σ : ℂ)).re := fun χ => hasSum_re_term χ hs1
  refine ⟨fun χ t => ?_, fun χ hχ => ?_, fun χ₁ χ₂ h₁ h₂ => ?_⟩
  · have hs2 : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
    have hs3 : 1 < ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I).re := by simpa using hσ
    have HS := (((H1 1).mul_left 3).add ((hasSum_re_term χ hs2).mul_left 4)).add
      (hasSum_re_term (χ ^ 2) hs3)
    have e : ((σ : ℂ) + 2 * t * I) = (σ : ℂ) + ((2 * t : ℝ) : ℂ) * I := by push_cast; ring
    rw [e]
    exact HasSum.nonneg (fun n => term_three_four_one_nonneg χ σ t n) HS
  · exact HasSum.nonneg (fun n => term_one_add_real_nonneg χ hχ σ n) ((H1 1).add (H1 χ))
  · exact HasSum.nonneg (fun n => term_two_real_nonneg χ₁ χ₂ h₁ h₂ σ n)
      ((((H1 1).add (H1 χ₁)).add (H1 χ₂)).add (H1 (χ₁ * χ₂)))
end Formalism.ZeroFreeDirichlet
