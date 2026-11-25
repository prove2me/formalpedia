-- Prove2me | solution 1 for Formalism.L2.Pj.frChartF_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:09:43.706889+00:00
-- url     : https://prove2.me/submissions/cded8164-7241-4b1c-a23d-ac0589b8174e

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnitIndepOfCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Theorems.Thm_Formalism_L2_Pj_frChart_of_cover
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
theorem _root_.solution (h : ChartCoverF Xo c) : FrChartF Xo c := by
  refine frChart_of_cover frMap_trans frMap_cancel fun S _ _ w m _ => ?_
  obtain ⟨A, u, cw, _, hu, _, hcl, hloc, _, _⟩ := h S w w rfl m
  exact ⟨A, u, cw, hu, hcl, hloc⟩
end Formalism.L2.Pj
