-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:49:01.682183+00:00
-- url     : https://prove2.me/submissions/3556d660-f780-4a8e-92e9-dc122bba2024

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_valS_sum_le
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_iff

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
variable {sg S}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {θ : ℝ} {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (L × Fin r) K)
    (h : ∀ i ∈ s, vala sg S θ (f i)) : vala sg S θ (∑ i ∈ s, f i) := by
  rw [vala_iff]
  exact valS_sum_le sg S s f _ fun i hi => (vala_iff sg S θ _).mp (h i hi)
end Formalism.MainNotions.PlaneGram
