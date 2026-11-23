-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.cro_ordGe_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:15.155725+00:00
-- url     : https://prove2.me/submissions/63a1851f-6f56-4865-8562-ed1992cc79f1

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd
import Theorems.Thm_Formalism_L2_Pj_Crude_OrdGe_mul
import Theorems.Thm_Formalism_L2_Pj_Crude_cro_ordGe_zero

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
theorem _root_.solution {t : ℕ} (g : PS k n d) {f : PS k n d} (hf : OrdGe t f) : OrdGe t (g * f) := by
  have h := OrdGe.mul (cro_ordGe_zero g) hf
  rwa [zero_add] at h
end Formalism.L2.Pj.Crude
