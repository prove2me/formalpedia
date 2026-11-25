-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.MapFB.map_DofN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:00:57.529991+00:00
-- url     : https://prove2.me/submissions/a1815b02-4a28-4fd5-8d62-21345eaadb70

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGaugeMapSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePNabMapSt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_MapFB_map_pderiv

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
theorem _root_.solution (F : Fin d → PS K 2 d) {n : ℕ} (b : Fin n) (u : Fin d → K) (f : PS K n d) :
    MvPowerSeries.map φ (DofN F b u f) =
      DofN (fun j => MvPowerSeries.map φ (F j)) b (fun i => φ (u i)) (MvPowerSeries.map φ f) := by
  unfold DofN
  simp only [map_sum, map_mul, MvPowerSeries.map_C,
    map_ev2 φ (pt K d b) 0 (fun i => cc_pt b i) zc_zero, mpt_pt, mpt_zero, map_pderiv]
end Formalism.L2.FormalSeriesBounds.MapFB
