-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.HomD_subX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:36:01.319278+00:00
-- url     : https://prove2.me/submissions/1db39594-8320-4406-8778-c75e753c4ef9

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_HomD_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_HomD_C_mul_X

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
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (x : L × Fin r) : HomD (ldeg (Finsupp.single x 1)) (subX sg S A B x) := by
  unfold subX
  split_ifs
  · exact HomD_sum _ _ fun b _ => HomD_C_mul_X _ x.1 b x.2
  · exact HomD_sum _ _ fun b _ => HomD_C_mul_X _ x.1 b x.2
  · have := HomD_C_mul_X (R := R) 1 x.1 x.2 x.2
    rwa [map_one, one_mul] at this
end Formalism.MainNotions.PlaneGram
