-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.MapFB.constantCoeff_eval_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:51:11.528381+00:00
-- url     : https://prove2.me/submissions/bb76d8cb-c010-435b-8c33-3413bb7e1716

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGaugeMapSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePNabMapSt
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
variable {K C : Type} [Field K] [Field C] (φ : K →+* C) {d : ℕ}
namespace Formalism.L2.FormalSeriesBounds.MapFB
theorem _root_.solution {n : ℕ} (a : Pt K n d) (ha : ∀ i, constantCoeff (a i) = 0) (f : PS K 1 d) :
    constantCoeff (ev ![a] f) = constantCoeff f :=
  cc_ev_eq _ (by intro j i; fin_cases j; simp [ha]) f
end Formalism.L2.FormalSeriesBounds.MapFB
