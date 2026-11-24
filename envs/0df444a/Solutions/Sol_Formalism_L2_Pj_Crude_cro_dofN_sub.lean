-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.cro_dofN_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:14:50.697836+00:00
-- url     : https://prove2.me/submissions/95a5c51e-bfe2-4833-9f55-79b927c2fa60

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
theorem _root_.solution (F : Fin d → PS k 2 d) (b : Fin n) (v : Fin d → k) (X Y : PS k n d) :
    DofN F b v (X - Y) = DofN F b v X - DofN F b v Y := by
  unfold DofN
  simp only [map_sub, mul_sub, Finset.sum_sub_distrib]
end Formalism.L2.Pj.Crude
