-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.cro_ordGe_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:14:53.128941+00:00
-- url     : https://prove2.me/submissions/05f7f7be-42ee-4300-a276-6a486a7036c2

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
theorem _root_.solution {t : ℕ} {f g : PS k n d} (hf : OrdGe t f) (hg : OrdGe t g) : OrdGe t (f + g) := by
  intro m hm
  rw [map_add, hf m hm, hg m hm, add_zero]
end Formalism.L2.Pj.Crude
