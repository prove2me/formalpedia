-- Prove2me | solution 1 for Formalism.REAL.sum_sum_sub_sum_sum_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:10:14.770964+00:00
-- url     : https://prove2.me/submissions/3b743868-5670-46ce-9ee3-27e980f49ce0

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
theorem _root_.solution {A α β : Type*} [AddCommGroup A] [Fintype α] [Fintype β] (f : α → β → A)
    (g : β → α → A) :
    ∑ x, ∑ y, f x y - ∑ y, ∑ x, g y x = ∑ x, ∑ y, (f x y - g y x) := by
  simp only [Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm
end Formalism.REAL
