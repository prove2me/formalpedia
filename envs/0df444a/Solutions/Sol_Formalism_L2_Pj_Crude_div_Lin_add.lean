-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.div_Lin_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:14:44.170173+00:00
-- url     : https://prove2.me/submissions/3e03c45e-e809-4033-b865-c8753ddf243b

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeDiv

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (b : Fin n) (v : Fin d → k) (f g : PS k n d) :
    Lin b v (f + g) = Lin b v f + Lin b v g := by
  simp only [Lin, map_add, mul_add, Finset.sum_add_distrib]
end Formalism.L2.Pj.Crude
