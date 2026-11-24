-- Prove2me | solution 1 for Formalism.REAL.bilinear_product_commutator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:42:16.639443+00:00
-- url     : https://prove2.me/submissions/5ea4e7e9-8b5f-4f2f-a09d-ca6fb4e00e8d

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft
import Theorems.Thm_Formalism_REAL_bilinear_commutator_identity

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
theorem _root_.solution (i j k l : Fin m) (a b c d : Fin n) :
    P i a * B j b * (P k c * B l d) - P k c * B l d * (P i a * B j b) =
      (if j = k ∧ b = c then 1 else 0) * (P i a * B l d) -
        (if l = i ∧ d = a then 1 else 0) * (P k c * B j b) :=
  bilinear_commutator_identity _ _ _ _ _ _ (hBP j k b c) (hBP l i d a) (hPP i k a c) (hBB j l b d)
    (by split_ifs <;> simp) (by split_ifs <;> simp)
end Formalism.REAL
