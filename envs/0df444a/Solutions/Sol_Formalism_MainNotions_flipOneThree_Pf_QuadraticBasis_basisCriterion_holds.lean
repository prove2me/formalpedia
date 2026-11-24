-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.basisCriterion_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:07:00.749582+00:00
-- url     : https://prove2.me/submissions/19a01d88-4a56-4a32-8ff7-e85ce9743aed

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_StatementO
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_QuadBasis
import Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_QuadraticBasis_qb_indep
import Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_QuadraticBasis_qb_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
namespace Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
theorem _root_.solution : QuadBasis := by
  intro p n' hp W O _ _ _ _ _ _ j w θ hpW cW hfin hw2 hw cO hθ x
  obtain ⟨a, b, c, d, hx⟩ := qb_span hp j w θ hpW cW hfin hw2 hw cO hθ x
  refine ⟨(a, b, c, d), hx, ?_⟩
  rintro ⟨a', b', c', d'⟩ hx'
  simp only at hx'
  have h : j (a' - a) + j (b' - b) * θ + j (c' - c) * w + j (d' - d) * θ * w = 0 := by
    simp only [map_sub]
    linear_combination hx - hx'
  obtain ⟨h1, h2, h3, h4⟩ := qb_indep j w θ hpW hw2 hw hθ h
  rw [sub_eq_zero.1 h1, sub_eq_zero.1 h2, sub_eq_zero.1 h3, sub_eq_zero.1 h4]
end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
