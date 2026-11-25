-- Prove2me | solution 1 for Formalism.REAL.casimir_bilinearRight_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:58:22.043151+00:00
-- url     : https://prove2.me/submissions/cb258bd5-e1ee-40cb-a324-688bb447797a

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft
import Theorems.Thm_Formalism_REAL_lower_mul_raise
import Theorems.Thm_P2M_Formalism_REAL_sum_sum_sum_sum_comm__604324486430

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
omit hPP
namespace Formalism.REAL
theorem _root_.solution :
    ∑ a, ∑ b, bilinearRight B P a b * bilinearRight B P b a = bilinearQuartic B P + n • bilinearNumber B P := by
  have e : ∀ i j a b, P i b * B i a * (P j a * B j b) =
      P i b * P j a * B j b * B i a + (if i = j then P i b * B j b else 0) := by
    intro i j a b
    rw [show P i b * B i a * (P j a * B j b) = P i b * (B i a * P j a) * B j b by
      simp only [mul_assoc], lower_mul_raise hBP i j a a]
    by_cases h : i = j
    · subst h
      simp [mul_add, add_mul, mul_assoc, hBB i i a b]
    · simp [h, mul_assoc, hBB i j a b]
  have h1 : ∑ a, ∑ b, ∑ i, ∑ j, P i b * P j a * B j b * B i a = bilinearQuartic B P := by
    rw [sum_sum_sum_sum_comm']
    unfold bilinearQuartic
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
  have h2 : ∑ a : Fin n, ∑ b, ∑ i, ∑ j, (if i = j then P i b * B j b else 0) = n • bilinearNumber B P := by
    unfold bilinearNumber
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    congr 1
    exact Finset.sum_comm
  simp only [bilinearRight, Finset.sum_mul_sum, e, Finset.sum_add_distrib]
  rw [h1, h2]
end Formalism.REAL
