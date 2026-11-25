-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.GlX.tr_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:21:18.180305+00:00
-- url     : https://prove2.me/submissions/1b9ae180-de89-4720-84b8-f8f448fad97c

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_GlX_tr_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM.DimensionMonotonicity Finset
open Formalism.CountingSumsFrames.TO.GlX
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
namespace Formalism.CountingSumsFrames.TO.GlX
theorem _root_.solution {h h' : V} (hk : LinearMap.ker (Lv G h) ≤ LinearMap.ker (Lv G h')) (y : LinearMap.range (Lv G h)) :
    tr G hk y ∈ LinearMap.range (Lv G h') := by
  obtain ⟨y, hy⟩ := y
  obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hy
  rw [show tr G hk ⟨Lv G h c, hy⟩ = Lv G h' c from tr_apply G hk c]
  exact LinearMap.mem_range_self _ _
end Formalism.CountingSumsFrames.TO.GlX
