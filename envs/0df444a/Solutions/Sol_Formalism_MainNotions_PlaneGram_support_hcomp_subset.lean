-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.support_hcomp_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:17:48.188082+00:00
-- url     : https://prove2.me/submissions/03015dfe-6178-4ee9-8f6e-dc1a29a15764

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_coeff_hcomp

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
    (hcomp d F).support ⊆ F.support := by
  intro β hβ
  rw [mem_support_iff, coeff_hcomp] at hβ
  rw [mem_support_iff]
  intro h0
  apply hβ
  rw [h0, ite_self]
end Formalism.MainNotions.PlaneGram
