-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.subst_inCol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:57:17.403305+00:00
-- url     : https://prove2.me/submissions/52d72602-25dd-4cc4-ad23-d5854eeb741e

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePAxesSelfSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePCartSelfSt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_hasSubst_col
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {τ : Type} {a : Fin 2 × Fin dd → MvPowerSeries τ C} (ha : ∀ x, constantCoeff (a x) = 0)
    (col : Fin 2) (f : MvPowerSeries (Fin dd) C) :
    subst a (inCol col f) = subst (fun i => a (col, i)) f := by
  have hS := hasSubst_of_constantCoeff_zero ha
  unfold inCol
  rw [subst_comp_subst_apply (hasSubst_col col) hS]
  congr 1
  funext i
  rw [subst_X hS]
end Formalism.L2.FormalSeriesBounds
