-- Prove2me | solution 1 for Formalism.L2.Pj.unitIndep_of_charts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:10:52.287284+00:00
-- url     : https://prove2.me/submissions/288a37e6-60e4-4a0b-8682-c1e9e031795f

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameProofs
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartWD
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnitIndepOfCharts
import Theorems.Thm_Formalism_L2_Pj_wtField_of_borChart
import Theorems.Thm_Formalism_L2_Pj_intDiagUnit_of
import Theorems.Thm_Formalism_L2_Pj_unitIndep_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
namespace Formalism.L2.Pj
theorem _root_.solution (h : BorChartF Xo c) (hL : IntLatU Xo c) : UnitIndep Xo c :=
  unitIndep_of (wtField_of_borChart h) (intDiagUnit_of hL)
end Formalism.L2.Pj
