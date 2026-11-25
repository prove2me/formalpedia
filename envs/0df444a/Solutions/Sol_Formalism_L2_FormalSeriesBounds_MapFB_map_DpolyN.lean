-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.MapFB.map_DpolyN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:29:33.254452+00:00
-- url     : https://prove2.me/submissions/accd30ed-11ab-411f-9d9f-9133846eb0aa

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGaugeMapSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePNabMapSt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_MapFB_map_DmonN

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
theorem _root_.solution (F : Fin d → PS K 2 d) {n : ℕ} {ι : Type} [Fintype ι] (cp : ι → Fin n)
    (u : ι → Fin d → K) (P : MvPolynomial ι K) (f : PS K n d) :
    MvPowerSeries.map φ (DpolyN F cp u P f) =
      DpolyN (fun j => MvPowerSeries.map φ (F j)) cp (fun l i => φ (u l i)) (MvPolynomial.map φ P)
        (MvPowerSeries.map φ f) := by
  unfold DpolyN
  rw [map_sum, MvPolynomial.support_map_of_injective P φ.injective]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, MvPowerSeries.map_C, MvPolynomial.coeff_map, map_DmonN]
end Formalism.L2.FormalSeriesBounds.MapFB
