-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.coeff_substS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:43.820838+00:00
-- url     : https://prove2.me/submissions/679c14e0-f731-43f6-9381-7e4c4e0d0fe2

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_substS_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} {R : Type} [CommRing R]
  (ι : K →+* R) (sg : L → Bool) (S : Finset L) (A B : Matrix (Fin r) (Fin r) R)
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (F : MvPolynomial (L × Fin r) K) (β : L × Fin r →₀ ℕ) :
    (substS ι sg S A B F).coeff β =
      ∑ α ∈ F.support, ι (F.coeff α) * (substS ι sg S A B (monomial α 1)).coeff β := by
  rw [substS_eq_sum, coeff_sum]
  exact Finset.sum_congr rfl fun α _ => coeff_C_mul _ _ _
end Formalism.MainNotions.PlaneGram
