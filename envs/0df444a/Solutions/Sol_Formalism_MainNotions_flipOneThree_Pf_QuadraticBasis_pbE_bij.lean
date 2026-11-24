-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.pbE_bij
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:08:47.463796+00:00
-- url     : https://prove2.me/submissions/bc97e820-8e46-4587-9f26-1af299a06e30

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_StatementO
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_PresIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
variable {W O : Type} [CommRing W] [CommRing O]
namespace Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
theorem _root_.solution {j : W →+* O} {θ w : O} (h : IsQuadBasis j θ w) : Function.Bijective (pbE j θ w) := by
  constructor
  · intro t s hts
    obtain ⟨u, -, hu⟩ := h (pbE j θ w t)
    exact (hu t rfl).trans (hu s hts).symm
  · intro x
    obtain ⟨t, ht, -⟩ := h x
    exact ⟨t, ht.symm⟩
end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
