-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.Aset_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:35:54.661299+00:00
-- url     : https://prove2.me/submissions/0a29e9fb-de07-48e5-a47b-b2ff58cbc6e7

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_smul_le


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
variable {K : Type} [Field K]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L) (n : ℤ) (a : K)
    {F : MvPolynomial (L × Fin r) K} (h : F ∈ Aset sg S n) : a • F ∈ Aset sg S n := by
  exact le_trans h (valS_smul_le sg S a F)
end Formalism.MainNotions.PlaneGram
