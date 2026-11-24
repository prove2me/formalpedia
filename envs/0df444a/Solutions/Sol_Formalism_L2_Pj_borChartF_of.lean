-- Prove2me | solution 1 for Formalism.L2.Pj.borChartF_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:37:40.625346+00:00
-- url     : https://prove2.me/submissions/7a89f773-a341-40a5-896b-bdc139f2a005

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnitIndepOfCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Theorems.Thm_Formalism_L2_Pj_borChart_of_cover
import Theorems.Thm_Formalism_L2_Pj_frMap_trans
import Theorems.Thm_Formalism_L2_Pj_frMap_cancel

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
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
variable {Xo c}
namespace Formalism.L2.Pj
theorem _root_.solution (h : ChartCoverF Xo c) (hB : FrBorBCF Xo c) : BorChartF Xo c := by
  refine borChart_of_cover frMap_trans frMap_cancel hB fun S _ _ t w w' hb m _ => ?_
  exact h S w w' hb.1 m
end Formalism.L2.Pj
