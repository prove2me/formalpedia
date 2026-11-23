-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.hcomp_mem_PolK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:16.599039+00:00
-- url     : https://prove2.me/submissions/7875537c-9d56-46b4-bbf3-fcd0da9ce76f

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
theorem _root_.solution (d : L → ℕ) (F : MvPolynomial (L × Fin r) K) : hcomp d F ∈ PolK K r d := by
  rw [mem_PolK_iff]
  intro α hα
  rw [mem_support_iff, coeff_hcomp] at hα
  by_contra h
  exact hα (if_neg h)
end Formalism.MainNotions.PlaneGram
