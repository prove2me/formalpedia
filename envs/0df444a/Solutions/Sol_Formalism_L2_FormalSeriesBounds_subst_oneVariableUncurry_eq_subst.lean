-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.subst_oneVariableUncurry_eq_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:20:51.674689+00:00
-- url     : https://prove2.me/submissions/8cc07cb0-e0de-4ee8-b4ac-848ddeaef082

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_hasSubst_snd
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_uncurry_eq_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {σ : Type} [Finite σ] {b : σ → PS C 1 dd} (hb : ∀ s, MvPowerSeries.constantCoeff (b s) = 0)
    (f : MvPowerSeries σ C) :
    un1 (MvPowerSeries.subst b f) = MvPowerSeries.subst (fun s => un1 (b s)) f := by
  have hB : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  rw [uncurry_eq_subst, MvPowerSeries.subst_comp_subst_apply hB hasSubst_snd]
  congr 1
  funext s
  rw [uncurry_eq_subst]
end Formalism.L2.FormalSeriesBounds
