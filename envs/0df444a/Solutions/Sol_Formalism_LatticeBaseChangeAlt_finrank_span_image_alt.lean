-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.finrank_span_image_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:51:13.740486+00:00
-- url     : https://prove2.me/submissions/3d610857-d7c7-469a-bf76-260c9b6c8ff8

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_BetaSesquilinearity
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LinearIndependentOfIsBaseChange
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_linearIndependent_of_isBaseChange_alt
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_span_image_span_alt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : FinrankSpanImage := by
  intro O O' K K' V V₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj V'
  let b := Module.finBasis K V'
  let w : Fin (finrank K V') → V := V'.subtype ∘ b
  have hw : LinearIndependent K w := b.linearIndependent.map' V'.subtype V'.ker_subtype
  have hspan : Submodule.span K (Set.range w) = V' := by
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
  have h1 : Submodule.span K' (j '' (V' : Set V)) =
      Submodule.span K' (Set.range (fun i => j (w i))) := by
    have h2 := span_image_span_alt (K' := K') j (Set.range w)
    rw [hspan] at h2
    rw [h2, ← Set.range_comp]
    rfl
  rw [h1, finrank_span_eq_card (linearIndependent_of_isBaseChange_alt j hj w hw), Fintype.card_fin]
end Formalism.LatticeBaseChangeAlt
