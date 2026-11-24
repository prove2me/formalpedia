-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.cro_lin_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:14:51.930578+00:00
-- url     : https://prove2.me/submissions/21741877-10fa-44fb-9ff6-1a53bbcbb03e

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd

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
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (b : Fin n) (v : Fin d → k) (X Y : PS k n d) : Lin b v (X - Y) = Lin b v X - Lin b v Y := by
  unfold Lin
  simp only [map_sub, mul_sub, Finset.sum_sub_distrib]
end Formalism.L2.Pj.Crude
