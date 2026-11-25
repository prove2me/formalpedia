-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.MapFB.constantCoeff_eval_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:45:30.486052+00:00
-- url     : https://prove2.me/submissions/221adc9a-0b42-4bb4-92cc-094c29594ecb

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePFBMapSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGaugeMapSt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_MapFB_cc_ev_eq

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.MapFB
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {R : Type} [CommRing R] {d : ℕ}
namespace Formalism.L2.FormalSeriesBounds.MapFB
theorem _root_.solution {n : ℕ} (a b : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (f : PS R 2 d) :
    constantCoeff (ev ![a, b] f) = constantCoeff f := cc_ev_eq ![a, b] (by intro j i; fin_cases j <;> simp [ha, hb]) f
end Formalism.L2.FormalSeriesBounds.MapFB
