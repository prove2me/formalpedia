-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.lg_addOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:28:38.797209+00:00
-- url     : https://prove2.me/submissions/7359226e-084c-4c1b-9175-e2a8e63c6a74

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_eval_points_two
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_const
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_eval_single_eq_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_singlePointUncurry
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_const
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (Y : FBChart C V O dd) {τ : Type} (P : Fin 2 → Fin dd → MvPowerSeries τ C)
    (hP : ∀ k j, MvPowerSeries.constantCoeff (P k j) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun j => MvPowerSeries.subst (fun q : Fin 2 × Fin dd => P q.1 q.2) (Y.B.G.F j))
        (un1 (Y.lg i)) =
      MvPowerSeries.subst (P 0) (un1 (Y.lg i)) + MvPowerSeries.subst (P 1) (un1 (Y.lg i)) := by
  have hPP : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd => P q.1 q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hP q.1 q.2
  have hF0 : ∀ j, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => P q.1 q.2) (Y.B.G.F j)) = 0 :=
    fun j => MvPowerSeries.constantCoeff_subst_eq_zero hPP (fun q => hP q.1 q.2) (Y.B.G.const j)
  rw [subst_singlePointUncurry hF0, subst_singlePointUncurry (hP 0), subst_singlePointUncurry (hP 1)]
  have key := congrArg (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => P q.1 q.2)) (Y.lg_add i)
  have hadd : addOf Y.B.G.F (pt C dd 0) (pt C dd 1) = Y.B.G.F := by
    funext j
    exact eval_points_two (Y.B.G.F j)
  have hA : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => Y.B.G.F q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => Y.B.G.const q.2
  have hX : ∀ k : Fin 2, MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => pt C (n := 2) dd k q.2) :=
    fun k => MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => MvPowerSeries.constantCoeff_X _
  rw [hadd, eval_single_eq_subst, eval_single_eq_subst, eval_single_eq_subst, MvPowerSeries.subst_add hPP,
    MvPowerSeries.subst_comp_subst_apply hA hPP, MvPowerSeries.subst_comp_subst_apply (hX 0) hPP,
    MvPowerSeries.subst_comp_subst_apply (hX 1) hPP] at key
  simp only [pt, MvPowerSeries.subst_X hPP] at key
  exact key
end Formalism.L2.FormalSeriesBounds
