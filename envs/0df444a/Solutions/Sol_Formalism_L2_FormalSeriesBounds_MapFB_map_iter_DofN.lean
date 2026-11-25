-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.MapFB.map_iter_DofN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:13:57.97344+00:00
-- url     : https://prove2.me/submissions/78f3fd85-1c6d-4af3-9baa-53cfe7fc4195

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGaugeMapSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePNabMapSt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_MapFB_map_DofN
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero


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
theorem _root_.solution (F : Fin d → PS K 2 d) {n : ℕ} (b : Fin n) (u : Fin d → K) (m : ℕ) (f : PS K n d) :
    MvPowerSeries.map φ ((DofN F b u)^[m] f) =
      (DofN (fun j => MvPowerSeries.map φ (F j)) b (fun i => φ (u i)))^[m] (MvPowerSeries.map φ f) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_DofN, ih]
end Formalism.L2.FormalSeriesBounds.MapFB
