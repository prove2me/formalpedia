-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.valS_C_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:03:57.546215+00:00
-- url     : https://prove2.me/submissions/ccf813ea-ddd2-4cc1-ba08-e76d78cc7403

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_mul_le
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_C_nonneg

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
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L)
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (a : K) (F : MvPolynomial (L × Fin r) K) :
    valS sg S F ≤ valS sg S (C a * F) := by
  have h := valS_mul_le sg S (C a) F
  refine le_trans ?_ h
  calc valS sg S F = 0 + valS sg S F := (zero_add _).symm
    _ ≤ _ := add_le_add (valS_C_nonneg sg S a) le_rfl
end Formalism.MainNotions.PlaneGram
