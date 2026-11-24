-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.valS_C_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:32:29.025249+00:00
-- url     : https://prove2.me/submissions/296eb983-1f41-4fe0-a8c1-c2d008f5c1de

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lord_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lord_C_nonneg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_le_valS_iff
import Theorems.Thm_Formalism_MainNotions_PlaneGram_subV_C

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
theorem _root_.solution (a : K) : 0 ≤ valS sg S (C a : MvPolynomial (L × Fin r) K) := by
  classical
  rw [le_valS_iff, subV_C]
  intro β
  rw [coeff_C]
  split_ifs
  · exact lord_C_nonneg _
  · rw [lord_zero]; exact le_top
end Formalism.MainNotions.PlaneGram
