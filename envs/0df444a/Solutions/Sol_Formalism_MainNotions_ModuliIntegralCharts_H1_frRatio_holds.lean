-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.frRatio_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:18:26.27738+00:00
-- url     : https://prove2.me/submissions/351a10e0-84d7-4dd0-93db-4862512f1ebd

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFixAsm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FrRatio
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FrRatio_frRatioG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution : FrRatioSt := by
  intro E _ _ _ H Dw l Xo c _ hstar S _ _ _ y C m
  have hch : L2.Pj.IsChartG Xo.univ.t y.x C.d C.B.G.F C.B.A.act _ C.uvec C.x :=
    ⟨C.chart.zero, C.chart.trunc, C.chart.law, C.chart.act, C.chart.tan, C.chart.basis⟩
  exact FrRatio.frRatioG hch ⟨C.frame.gen, C.frame.ph1, C.frame.ph2, C.frame.sy, C.frame.ad⟩ m
end Formalism.MainNotions.ModuliIntegralCharts.H1
