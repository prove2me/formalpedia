-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.hcomp_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:17:26.4348+00:00
-- url     : https://prove2.me/submissions/8c205059-25c8-45f0-b2af-bb42feba3a06

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_hcomp
import Theorems.Thm_Formalism_MainNotions_PlaneGram_mem_PolK_iff


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
theorem _root_.solution (d : L → ℕ) (F : MvPolynomial (L × Fin r) K) (hF : F ∈ PolK K r d) :
    hcomp d F = F := by
  ext β
  rw [coeff_hcomp]
  split_ifs with h
  · rfl
  · by_contra hne
    exact h ((mem_PolK_iff d F).mp hF β (mem_support_iff.mpr (Ne.symm hne)))
end Formalism.MainNotions.PlaneGram
