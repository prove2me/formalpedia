-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.cro_ordGe_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:14:56.378744+00:00
-- url     : https://prove2.me/submissions/8f50a22c-d133-4b9b-95fb-e49771fb59a7

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd
import Theorems.Thm_Formalism_L2_Pj_Crude_cro_ordGe_sum
import Theorems.Thm_Formalism_L2_Pj_Crude_cro_ordGe_mul_left
import Theorems.Thm_Formalism_L2_Pj_Crude_cro_ordGe_pderiv

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
theorem _root_.solution {t : ℕ} {f : PS k n d} (hf : OrdGe (t + 1) f) (b : Fin n) (v : Fin d → k) :
    OrdGe t (Lin b v f) := by
  unfold Lin
  exact cro_ordGe_sum _ _ fun j _ => cro_ordGe_mul_left _ (cro_ordGe_pderiv hf _)
end Formalism.L2.Pj.Crude
