-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.substS_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:08:45.551512+00:00
-- url     : https://prove2.me/submissions/dce1adfa-2be8-4f6b-94f0-e20432b092d2

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_substS_monomial__39ec68064bef

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
theorem _root_.solution (F : MvPolynomial (L × Fin r) K) :
    substS ι sg S A B F =
      ∑ α ∈ F.support, C (ι (F.coeff α)) * substS ι sg S A B (monomial α 1) := by
  conv_lhs => rw [F.as_sum, map_sum]
  exact Finset.sum_congr rfl fun α _ => substS_monomial' ι sg S A B α _
end Formalism.MainNotions.PlaneGram
