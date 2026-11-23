-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.cro_ordGe_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:32.401446+00:00
-- url     : https://prove2.me/submissions/855a0ec7-cca5-41e9-9196-25697e7fcf55

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
theorem _root_.solution {t : ℕ} {ι : Type} (s : Finset ι) (f : ι → PS k n d) (hf : ∀ i ∈ s, OrdGe t (f i)) :
    OrdGe t (∑ i ∈ s, f i) := by
  intro m hm
  rw [map_sum]
  exact Finset.sum_eq_zero fun i hi => hf i hi m hm
end Formalism.L2.Pj.Crude
