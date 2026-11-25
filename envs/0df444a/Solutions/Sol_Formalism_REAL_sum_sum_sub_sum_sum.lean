-- Prove2me | solution 1 for Formalism.REAL.sum_sum_sub_sum_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:19:24.77733+00:00
-- url     : https://prove2.me/submissions/4815d05f-46aa-42ed-a598-9c47526dcc9c

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {A α β : Type*} [AddCommGroup A] [Fintype α] [Fintype β] (f g : α → β → A) :
    ∑ x, ∑ y, f x y - ∑ x, ∑ y, g x y = ∑ x, ∑ y, (f x y - g x y) := by
  simp only [Finset.sum_sub_distrib]
end Formalism.REAL
