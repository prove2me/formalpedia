-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.hcomp_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:17:19.757391+00:00
-- url     : https://prove2.me/submissions/c68fef1d-c9e5-45ae-8172-a828deccd26c

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_hcomp_eq_dg

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
variable {L : Type} {r : ℕ}
variable {K : Type} [Field K] [DecidableEq L] {R : Type} [CommRing R]
  (ι : K →+* R) (sg : L → Bool) (S : Finset L) (A B : Matrix (Fin r) (Fin r) R)
variable [Fintype L]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (d : L → ℕ) (F G : MvPolynomial (L × Fin r) K) :
    hcomp d (F + G) = hcomp d F + hcomp d G := by
  simp only [hcomp_eq_dg, map_add]
end Formalism.MainNotions.PlaneGram
