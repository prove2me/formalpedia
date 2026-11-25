-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero.lgS_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:41:28.96775+00:00
-- url     : https://prove2.me/submissions/9660e53b-dfed-4e30-9201-862a5676bee6

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_UncurryLogConstantCoeff
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjugateGermZero_hasSubst_col
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjugateGermZero_hasSubst_tau
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjugateGermZero_lawS_const
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjugateGermZero_fb_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjugateGermZero_lg_self
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_const
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
open Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ FormalGermZero GeneralGermZero
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
variable {d : ℕ} {I0 : Type} [Fintype I0]
namespace Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
theorem _root_.solution (Y : FBChart C V O dd) (p : SelfData Y d I0) : LgAdd (lawS Y) (Y.rawSelf p).lg := by
  intro k
  have hL : MvPowerSeries.HasSubst (lawS Y) := MvPowerSeries.hasSubst_of_constantCoeff_zero (lawS_const Y)
  have hc : MvPowerSeries.HasSubst
      (fun i : Fin dd => (MvPowerSeries.X (k.1, i) : MvPowerSeries (Fin 2 × Fin dd) C)) := hasSubst_col k.1
  have hτ : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd =>
      (MvPowerSeries.X (q.1, (k.1, q.2)) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) := hasSubst_tau k.1
  have hF : MvPowerSeries.HasSubst Y.B.G.F := MvPowerSeries.hasSubst_of_constantCoeff_zero Y.B.G.const
  have hX0 := MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin 2 × Fin dd => (MvPowerSeries.X ((0 : Fin 2), q) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) (fun _ => by simp)
  have hX1 := MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin 2 × Fin dd => (MvPowerSeries.X ((1 : Fin 2), q) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) (fun _ => by simp)
  have hY0 := MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin dd => (MvPowerSeries.X ((0 : Fin 2), q) : MvPowerSeries (Fin 2 × Fin dd) C)) (fun _ => by simp)
  have hY1 := MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin dd => (MvPowerSeries.X ((1 : Fin 2), q) : MvPowerSeries (Fin 2 × Fin dd) C)) (fun _ => by simp)
  rw [lg_self Y p k, MvPowerSeries.subst_comp_subst_apply hc hL, MvPowerSeries.subst_comp_subst_apply hc hX0,
    MvPowerSeries.subst_comp_subst_apply hc hX1]
  simp only [MvPowerSeries.subst_X hL, MvPowerSeries.subst_X hX0, MvPowerSeries.subst_X hX1]
  rw [show (fun i : Fin dd => lawS Y (k.1, i)) = fun i => MvPowerSeries.subst (fun q : Fin 2 × Fin dd =>
      (MvPowerSeries.X (q.1, (k.1, q.2)) : MvPowerSeries (Fin 2 × (Fin 2 × Fin dd)) C)) (Y.B.G.F i) from rfl,
    ← MvPowerSeries.subst_comp_subst_apply hF hτ, fb_add Y k.2, MvPowerSeries.subst_add hτ,
    MvPowerSeries.subst_comp_subst_apply hY0 hτ, MvPowerSeries.subst_comp_subst_apply hY1 hτ]
  simp only [MvPowerSeries.subst_X hτ]
end Formalism.L2.FormalSeriesBounds.SelfConjugateGermZero
