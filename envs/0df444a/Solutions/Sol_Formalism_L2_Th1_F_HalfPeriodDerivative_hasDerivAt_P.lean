-- Prove2me | solution 1 for Formalism.L2.Th1.F.HalfPeriodDerivative.hasDerivAt_P
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:09.470894+00:00
-- url     : https://prove2.me/submissions/1ecccb06-90e0-424b-9230-6ac27300cbbf

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassPSecondDerivative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.HalfPeriodDerivative
namespace Formalism.L2.Th1.F.HalfPeriodDerivative
theorem _root_.solution (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
  have h := (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
  rwa [L.deriv_weierstrassP] at h
end Formalism.L2.Th1.F.HalfPeriodDerivative
