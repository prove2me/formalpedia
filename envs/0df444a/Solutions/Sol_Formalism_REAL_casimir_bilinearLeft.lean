-- Prove2me | solution 1 for Formalism.REAL.casimir_bilinearLeft
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:34:09.026449+00:00
-- url     : https://prove2.me/submissions/98956fc0-89e4-442b-a2d7-3096a74d056e

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft
import Theorems.Thm_Formalism_REAL_lower_mul_raise

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.REAL
variable {A : Type*} [Ring A] {m n : ℕ} (B P : Fin m → Fin n → A)
variable {B P}
variable (hBP : ∀ i j a b, B i a * P j b - P j b * B i a = if i = j ∧ a = b then 1 else 0)
  (hBB : ∀ i j a b, B i a * B j b = B j b * B i a)
  (hPP : ∀ i j a b, P i a * P j b = P j b * P i a)
include hBP hBB hPP
omit hBB hPP
namespace Formalism.REAL
theorem _root_.solution : Cas (bilinearLeft B P) = bilinearQuartic B P + m • bilinearNumber B P := by
  have e : ∀ i j a b, P i a * B j a * (P j b * B i b) =
      P i a * P j b * B j a * B i b + (if a = b then P i a * B i b else 0) := by
    intro i j a b
    rw [show P i a * B j a * (P j b * B i b) = P i a * (B j a * P j b) * B i b by
      simp only [mul_assoc], lower_mul_raise hBP j j a b]
    by_cases h : a = b
    · subst h
      simp [mul_add, add_mul, mul_assoc]
    · simp [h, mul_assoc]
  simp only [Cas, bilinearLeft, bilinearQuartic, bilinearNumber, Finset.sum_mul_sum, e, Finset.sum_add_distrib]
  congr 1
  simp [Finset.smul_sum]
end Formalism.REAL
