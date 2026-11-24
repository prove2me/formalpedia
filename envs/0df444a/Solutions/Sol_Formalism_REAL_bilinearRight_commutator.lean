-- Prove2me | solution 1 for Formalism.REAL.bilinearRight_commutator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:55:27.879961+00:00
-- url     : https://prove2.me/submissions/0d46587e-5ddf-48e9-ae8c-f03c714dbca4

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
theorem _root_.solution (a b c d : Fin n) :
    bilinearRight B P a b * bilinearRight B P c d - bilinearRight B P c d * bilinearRight B P a b =
      (if a = d then bilinearRight B P c b else 0) - (if c = b then bilinearRight B P a d else 0) := by
  simp only [bilinearRight, Finset.sum_mul_sum]
  rw [sum_sum_sub_sum_sum_swap]
  simp only [bilinear_product_commutator hBP hBB hPP]
  simp only [Finset.sum_sub_distrib]
  congr 1
  · by_cases h : a = d <;> simp [h, ite_mul]
  · by_cases h : c = b <;> simp [h, ite_mul]
end Formalism.REAL
