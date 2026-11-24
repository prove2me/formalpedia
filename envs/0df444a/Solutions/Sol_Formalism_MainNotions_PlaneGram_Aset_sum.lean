-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.Aset_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:49:04.545416+00:00
-- url     : https://prove2.me/submissions/67cad16d-c78f-4048-85dd-6c9a411380db

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_sum_le


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
theorem _root_.solution {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L) (n : ℤ) {ι : Type}
    (s : Finset ι) (f : ι → MvPolynomial (L × Fin r) K) (h : ∀ i ∈ s, f i ∈ Aset sg S n) :
    ∑ i ∈ s, f i ∈ Aset sg S n := by
  exact valS_sum_le sg S s f n h
end Formalism.MainNotions.PlaneGram
