-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.subst_singlePointUncurry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:14:37.041221+00:00
-- url     : https://prove2.me/submissions/c4668ad7-0c59-4982-bafe-ed595376c277

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_hasSubst_snd
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_uncurry_eq_subst
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
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
theorem _root_.solution {τ : Type} {a : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (f : PS C 1 dd) :
    MvPowerSeries.subst a (un1 f) = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => a p.2) f := by
  have hA : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  rw [uncurry_eq_subst, MvPowerSeries.subst_comp_subst_apply hasSubst_snd hA]
  congr 1
  funext p
  show MvPowerSeries.subst a (MvPowerSeries.X p.2) = a p.2
  rw [MvPowerSeries.subst_X hA]
end Formalism.L2.FormalSeriesBounds
