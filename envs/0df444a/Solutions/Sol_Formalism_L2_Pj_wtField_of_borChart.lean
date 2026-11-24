-- Prove2me | solution 1 for Formalism.L2.Pj.wtField_of_borChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:23:13.082405+00:00
-- url     : https://prove2.me/submissions/b7567b17-6d77-4b72-8104-d2cb68620832

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameProofs
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartWD
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnitIndepOfCharts
import Theorems.Thm_Formalism_L2_Pj_wtAll_of_borChart


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
theorem _root_.solution (h : BorChartF Xo c) : WtField Xo c := by
  intro a n f hf S _ _ t y y' hy hy' hb
  exact wtAll_of_borChart h (ex Dw a n) hf.1 hf.2 S t y y' hy hy' hb
end Formalism.L2.Pj
