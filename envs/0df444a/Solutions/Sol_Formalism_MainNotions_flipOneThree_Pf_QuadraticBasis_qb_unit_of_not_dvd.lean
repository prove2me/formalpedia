-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.qb_unit_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:09:35.46609+00:00
-- url     : https://prove2.me/submissions/1228fe5f-5aca-4caa-9264-50a9901a6a5a

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
theorem _root_.solution {p : ℕ} (hpW : Irreducible (p : W)) {b : W} (hb : ¬ (p : W) ∣ b) :
    IsUnit b := by
  by_contra h
  have h1 : b ∈ IsLocalRing.maximalIdeal W := (IsLocalRing.mem_maximalIdeal b).2 h
  rw [hpW.maximalIdeal_eq, Ideal.mem_span_singleton] at h1
  exact hb h1
end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
