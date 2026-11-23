-- Prove2me | solution 1 for Formalism.DimensionVariation.height_bound_complete
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:03.701099+00:00
-- url     : https://prove2.me/submissions/1c440f3a-c2af-40ec-a7ac-1a83f0231dc8

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqExplicit6
import Definitions.Def_Formalism_ThetaSupremumBounds_FinalJ
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GlobalBoundRefinements
import Theorems.Thm_Formalism_DimensionVariation_heightBound6_statement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
namespace Formalism.DimensionVariation
theorem _root_.solution : HeightRecord6 := by
  intro J Pl Emb Frm _ _ _ _ _ _ TT r ν g0 logB logP logK MainNotions loglam logOmτ logth0 logh logh' aT logH
    logOm v f m N S η b' nV L La L' logT logg C2 C3 C4 c5 c6 C7 C8 C hC1 hPs h32 hlm hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa h5 h6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  obtain ⟨cst, -, -, k1, k2, k3⟩ := heightBound6_statement J Pl Emb Frm r ν g0 logB logP logK MainNotions loglam logOmτ
    logth0 logh logh' (recordX logH f nV L' C) (recordA TT aT logT f m N S η b' La C)
    logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C hC1 hPs h32 hlm hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa h5 h6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  have e : recordHu TT ν aT logH logT logOm f m N S η b' nV L La L' C =
      recordA TT aT logT f m N S η b' La C +
        ∑ j, (sizeB ν logOm f m N L La C j - recordX logH f nV L' C j) := by
    unfold recordHu
    rw [Finset.sum_sub_distrib]
    ring
  rw [e]
  exact ⟨_, k1, k2, k3⟩
end Formalism.DimensionVariation
