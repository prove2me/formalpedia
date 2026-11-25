-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.MapFB.map_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:50:16.273793+00:00
-- url     : https://prove2.me/submissions/7d175fca-9f95-4885-9e5d-1272e30a1f3d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGaugeMapSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePNabMapSt

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
variable {K C : Type} [Field K] [Field C] (φ : K →+* C) {d : ℕ}
namespace Formalism.L2.FormalSeriesBounds.MapFB
theorem _root_.solution {σ : Type} (x : σ) (f : MvPowerSeries σ K) :
    MvPowerSeries.map φ (pderiv K x f) = pderiv C x (MvPowerSeries.map φ f) := by
  ext n
  simp [coeff_pderiv, coeff_map]
end Formalism.L2.FormalSeriesBounds.MapFB
