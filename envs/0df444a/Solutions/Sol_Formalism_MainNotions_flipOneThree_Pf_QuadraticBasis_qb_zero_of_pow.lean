-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.qb_zero_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:09:37.409438+00:00
-- url     : https://prove2.me/submissions/510e5482-da41-4d28-bafb-3c08c36b8283

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_StatementO
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_QuadBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
variable {W O : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
namespace Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
theorem _root_.solution {p : ℕ} (hpW : Irreducible (p : W)) {a : W} (h : ∀ m, (p : W) ^ m ∣ a) : a = 0 := by
  by_contra ha
  obtain ⟨n, hn⟩ := FiniteMultiplicity.of_not_isUnit hpW.not_isUnit ha
  exact hn (h _)
end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
