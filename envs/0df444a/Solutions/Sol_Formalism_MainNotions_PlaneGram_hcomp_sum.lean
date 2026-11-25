-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.hcomp_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:17:33.847973+00:00
-- url     : https://prove2.me/submissions/d3700c53-8b98-4688-a32a-39ead15a6a9e

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
theorem _root_.solution {κ : Type} (d : L → ℕ) (s : Finset κ) (f : κ → MvPolynomial (L × Fin r) K) :
    hcomp d (∑ k ∈ s, f k) = ∑ k ∈ s, hcomp d (f k) := by
  simp only [hcomp_eq_dg, map_sum]
end Formalism.MainNotions.PlaneGram
