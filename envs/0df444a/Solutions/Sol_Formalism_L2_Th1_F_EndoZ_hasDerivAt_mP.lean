-- Prove2me | solution 1 for Formalism.L2.Th1.F.EndoZ.hasDerivAt_mP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:13:25.087729+00:00
-- url     : https://prove2.me/submissions/8bb5d092-9397-4ba3-ab66-aa02c47382bb

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IntegerEndomorphismInstance
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_T_sub
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_wp_eq
import Theorems.Thm_Formalism_L2_Th1_F_EndoZ_ne_zero_of_notMem
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_add
import Theorems.Thm_Formalism_L2_Th1_F_LatOnly_wp_eq
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_add
import Theorems.Thm_Formalism_L2_Th1_F_zetaHasDeriv


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
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.EndoZ
open PowerSeries TaylorWp
namespace Formalism.L2.Th1.F.EndoZ
theorem _root_.solution (L : PeriodPair) {P w : ℂ} (hw : w ∈ U L P) :
    HasDerivAt (mP L P) (2 * L.weierstrassPExcept 0 w - L.weierstrassP (w + P)
      - L.weierstrassP (w - P)) w := by
  obtain ⟨hw0, hwp, hwm⟩ := hw
  have hne := ne_zero_of_notMem L hw0
  have h1 := (hasDerivAt_inv hne).const_mul 2
  have h2 := (zetaHasDeriv L _ hwp).comp w ((hasDerivAt_id' w).add_const P)
  have h3 := (zetaHasDeriv L _ hwm).comp w ((hasDerivAt_id' w).sub_const P)
  have h4 := (zetaHasDeriv L _ hw0).const_mul 2
  have h := ((h1.add h2).add h3).sub h4
  refine h.congr_deriv ?_
  rw [wp_eq L w]
  field_simp
  ring
end Formalism.L2.Th1.F.EndoZ
