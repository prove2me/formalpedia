-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.valS_hcomp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:28:52.306091+00:00
-- url     : https://prove2.me/submissions/88759107-f66d-40c1-bd04-470132daaef2

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lord_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_le_valS_iff
import Theorems.Thm_Formalism_MainNotions_PlaneGram_pge_valS
import Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_subV_hcomp

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
theorem _root_.solution (d : L → ℕ) (F : MvPolynomial (L × Fin r) K) :
    valS sg S F ≤ valS sg S (hcomp d F) := by
  rw [le_valS_iff]
  intro β
  rw [subV, coeff_subV_hcomp]
  split_ifs
  · exact pge_valS sg S F β
  · rw [lord_zero]; exact le_top
end Formalism.MainNotions.PlaneGram
