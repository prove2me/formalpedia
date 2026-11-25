-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.hcomp_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:17:30.661175+00:00
-- url     : https://prove2.me/submissions/bcb565a1-a2b8-4526-a53f-d98b5be85615

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
theorem _root_.solution (d : L → ℕ) (a : K) (F : MvPolynomial (L × Fin r) K) :
    hcomp d (a • F) = a • hcomp d F := by
  simp only [hcomp_eq_dg, map_smul]
end Formalism.MainNotions.PlaneGram
