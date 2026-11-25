-- Prove2me | solution 1 for Formalism.L2.Pj.borChartF_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:12:27.985037+00:00
-- url     : https://prove2.me/submissions/56d3b037-f8e1-481e-bfb0-fd2b28037c14

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnitIndepOfCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Theorems.Thm_Formalism_L2_Pj_borChartF_of
import Theorems.Thm_Formalism_L2_Pj_frBorBC

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
open MonObj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
namespace Formalism.L2.Pj
theorem _root_.solution (h : ChartCoverF Xo c) : BorChartF Xo c :=
  borChartF_of h frBorBC
end Formalism.L2.Pj
