-- Prove2me | solution 1 for Formalism.L2.Pj.exist3_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:36:41.540886+00:00
-- url     : https://prove2.me/submissions/5c91ec3c-d2b6-43f3-84cf-e7370466e3c4

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameProofs
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartWD
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnitIndepOfCharts
import Theorems.Thm_Formalism_L2_Pj_evalWD_fr
import Theorems.Thm_Formalism_L2_Pj_wtField_of_borChart
import Theorems.Thm_Formalism_L2_Pj_intDiagUnit_of


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
theorem _root_.solution (hC : FrChartF Xo c) (hB : BorChartF Xo c) (hL : IntLatU Xo c) :
    EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ∧ WtField Xo c ∧ IntDiagUnit Xo c :=
  ⟨evalWD_fr hC, wtField_of_borChart hB, intDiagUnit_of hL⟩
end Formalism.L2.Pj
