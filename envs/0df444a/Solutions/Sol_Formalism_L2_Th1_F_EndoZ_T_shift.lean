-- Prove2me | solution 1 for Formalism.L2.Th1.F.EndoZ.T_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:41:01.512427+00:00
-- url     : https://prove2.me/submissions/559b80c8-99db-4690-9043-a09606f4b745

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IntegerEndomorphismInstance
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_add
import Theorems.Thm_Formalism_L2_Th1_F_HalfPeriodDerivative_hasDerivAt_P
import Theorems.Thm_Formalism_L2_Th1_F_HalfPeriodDerivative_isOpen_compl
import Theorems.Thm_Formalism_L2_Th1_F_PDeriv_hasDerivAt_P
import Theorems.Thm_Formalism_L2_Th1_F_PeriodLatticeBasisLemmas_isOpen_compl
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_add
import Theorems.Thm_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_isOpen_compl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Filter Topology
namespace Formalism.L2.Th1.F
namespace EndoZ
open PowerSeries TaylorWp
private theorem analyticAt_weierstrassP_of_not_mem (L : PeriodPair) {P : ℂ} (hP : P ∉ L.lattice) :
    AnalyticAt ℂ L.weierstrassP P := by
  have hda : DifferentiableOn ℂ L.weierstrassP (L.lattice : Set ℂ)ᶜ := fun w hw =>
    (PDeriv.hasDerivAt_P L hw).differentiableAt.differentiableWithinAt
  exact hda.analyticAt ((PeriodPair.isClosed_lattice L).isOpen_compl.mem_nhds hP)
end EndoZ
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.EndoZ
open PowerSeries TaylorWp
namespace Formalism.L2.Th1.F.EndoZ
theorem _root_.solution (L : PeriodPair) {P : ℂ} (hP : P ∉ L.lattice) :
    T (fun z => L.weierstrassP (z + P)) (taylor0 fun z => L.weierstrassP (z + P)) := by
  refine ⟨?_, rfl⟩
  exact (analyticAt_weierstrassP_of_not_mem L hP).comp_of_eq (analyticAt_id.add analyticAt_const) (by simp)
end Formalism.L2.Th1.F.EndoZ
