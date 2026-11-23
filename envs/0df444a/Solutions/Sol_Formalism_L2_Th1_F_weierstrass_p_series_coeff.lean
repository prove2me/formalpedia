-- Prove2me | solution 1 for Formalism.L2.Th1.F.weierstrass_p_series_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:12:23.616318+00:00
-- url     : https://prove2.me/submissions/958abb57-83cd-4fee-8f7a-7092b6ce59ac

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open PowerSeries
open TaylorWp
namespace Formalism.L2.Th1.F
theorem _root_.solution : PSeriesCoeff := by
  intro L n
  rw [pSeries, taylor0, coeff_mk, L.iteratedDeriv_weierstrassPExcept_self 0]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, if_false, PeriodPair.sumInvPow_zero]
    have h : ((n.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    rw [Nat.factorial_succ]
    push_cast
    field_simp
end Formalism.L2.Th1.F
