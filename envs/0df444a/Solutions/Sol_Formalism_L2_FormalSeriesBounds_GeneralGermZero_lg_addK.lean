-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.GeneralGermZero.lg_addK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:20:08.871572+00:00
-- url     : https://prove2.me/submissions/eebb19e2-71ea-4015-b6e6-e24ce6a130f4

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_GeneralGermZero_pairK_const
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
open Formalism.L2.FormalSeriesBounds.GeneralGermZero
open Formalism.IncomingBounds FormalGermZero
variable {C : Type} [Field C] {κ : Type} [Fintype κ]
namespace Formalism.L2.FormalSeriesBounds.GeneralGermZero
theorem _root_.solution {σ : Type} (F : κ → MvPowerSeries (Fin 2 × κ) C) (hF0 : ∀ k, MvPowerSeries.constantCoeff (F k) = 0)
    (lg : κ → MvPowerSeries κ C) (hadd : LgAdd F lg) (a b : κ → MvPowerSeries σ C)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0) (k : κ) :
    MvPowerSeries.subst (addK F a b) (lg k) = MvPowerSeries.subst a (lg k) + MvPowerSeries.subst b (lg k) := by
  have hP : MvPowerSeries.HasSubst (fun q : Fin 2 × κ => ![a, b] q.1 q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (pairK_const ha hb)
  have hF : MvPowerSeries.HasSubst F := MvPowerSeries.hasSubst_of_constantCoeff_zero hF0
  have hX0 : MvPowerSeries.HasSubst
      (fun q : κ => (MvPowerSeries.X ((0 : Fin 2), q) : MvPowerSeries (Fin 2 × κ) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hX1 : MvPowerSeries.HasSubst
      (fun q : κ => (MvPowerSeries.X ((1 : Fin 2), q) : MvPowerSeries (Fin 2 × κ) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have e := congrArg (MvPowerSeries.subst (fun q : Fin 2 × κ => ![a, b] q.1 q.2)) (hadd k)
  rw [MvPowerSeries.subst_comp_subst_apply hF hP, MvPowerSeries.subst_add hP,
    MvPowerSeries.subst_comp_subst_apply hX0 hP, MvPowerSeries.subst_comp_subst_apply hX1 hP] at e
  simp only [MvPowerSeries.subst_X hP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e
  exact e
end Formalism.L2.FormalSeriesBounds.GeneralGermZero
