-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.segment_letter_first_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:40.813856+00:00
-- url     : https://prove2.me/submissions/2ca0e2b5-b8e9-4c15-99ea-e38d4eb52fbb

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_IntegralMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_range_first_embedding

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
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (k : Fin (D.nB j + D.r)) : D.SegL j (D.e0 j k) := by
  rcases (D.range_first_embedding j _).1 ⟨k, rfl⟩ with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
end Formalism.MainNotions.PlaneGram.TwistData
