-- Prove2me | solution 1 for Formalism.L2.Pj.evalWD_fr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:24:00.615874+00:00
-- url     : https://prove2.me/submissions/8d336fcc-ce61-40af-bc6a-4c60845d68fc

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameProofs
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartWD
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnitIndepOfCharts
import Theorems.Thm_Formalism_L2_Pj_evalWD_of_frChart


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
theorem _root_.solution (h : FrChartF Xo c) :
    EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) :=
  evalWD_of_frChart h
end Formalism.L2.Pj
