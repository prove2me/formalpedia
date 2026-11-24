-- Prove2me | solution 1 for Formalism.L2.Th1.F.SigmaBasic.differentiable_tprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:37:52.082341+00:00
-- url     : https://prove2.me/submissions/16f34d48-7e65-4746-aa05-e57a3894c4eb

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaBasic
import Theorems.Thm_Formalism_L2_Th1_F_SigmaBasic_differentiable_wFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.SigmaBasic
namespace Formalism.L2.Th1.F.SigmaBasic
theorem _root_.solution (h : SigmaProdLU) (L : PeriodPair) :
    Differentiable ℂ (fun z => ∏' l : L.lattice, wFactor (l : ℂ) z) := by
  rw [← differentiableOn_univ]
  refine TendstoLocallyUniformlyOn.differentiableOn (h L) ?_ isOpen_univ
  refine Eventually.of_forall fun s => ?_
  refine Differentiable.differentiableOn ?_
  intro x
  exact DifferentiableAt.fun_finset_prod fun l _ => differentiable_wFactor _ x
end Formalism.L2.Th1.F.SigmaBasic
