-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.substS_monomial_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:33:24.333249+00:00
-- url     : https://prove2.me/submissions/b3d52e94-ea26-4e7a-b0d8-13115ddd3064

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eOut_add_eIn
import Theorems.Thm_Formalism_MainNotions_PlaneGram_substS_monomial_of_free

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
variable (out : L → Prop) [DecidablePred out]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (hout : ∀ i ∈ S, ¬ out i) (α : L × Fin r →₀ ℕ) :
    substS ι sg S A B (monomial α 1) =
      monomial (eOut out α) 1 * substS ι sg S A B (monomial (eIn out α) 1) := by
  have h1 : (monomial α (1 : K)) = monomial (eOut out α) 1 * monomial (eIn out α) 1 := by
    rw [monomial_mul, eOut_add_eIn, one_mul]
  conv_lhs => rw [h1, map_mul]
  rw [substS_monomial_of_free ι sg S A B (eOut out α) 1, map_one]
  intro x hx hxS
  rw [Finsupp.mem_support_iff, eOut_apply, if_neg (hout _ hxS)] at hx
  exact hx rfl
end Formalism.MainNotions.PlaneGram
