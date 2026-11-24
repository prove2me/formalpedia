-- Prove2me | solution 1 for Formalism.REAL.bilinearLeft_mul_bilinearRight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:55:27.041919+00:00
-- url     : https://prove2.me/submissions/c4d74be8-5c08-441e-9dfa-5141901462a6

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft
import Theorems.Thm_Formalism_REAL_sum_sum_sub_sum_sum_swap
import Theorems.Thm_Formalism_REAL_bilinear_product_commutator

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
namespace Formalism.REAL
theorem _root_.solution (i j : Fin m) (a b : Fin n) :
    bilinearLeft B P i j * bilinearRight B P a b = bilinearRight B P a b * bilinearLeft B P i j := by
  rw [← sub_eq_zero]
  simp only [bilinearLeft, bilinearRight, Finset.sum_mul_sum]
  rw [sum_sum_sub_sum_sum_swap]
  simp only [bilinear_product_commutator hBP hBB hPP]
  simp only [Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  simp [ite_and, ite_mul]
end Formalism.REAL
