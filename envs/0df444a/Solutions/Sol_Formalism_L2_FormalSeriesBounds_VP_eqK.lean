-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.eqK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:51:40.53168+00:00
-- url     : https://prove2.me/submissions/0c26f4f5-65a8-4b19-876d-4e269c021968

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PullbackLogCoordsEvalZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_l
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_e
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_exlg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_lgex
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_hs
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_one_iff
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_pderiv_subst


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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
variable (Y : FBChart C V O dd)
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution (n k : Fin dd) :
    ∑ m, J Y m k * MvPowerSeries.pderiv C m (e Y n) = if n = k then 1 else 0 := by

  have hl := fun w => (ordGE_one_iff (l Y w)).2 (cc_l Y w)
  have hsE : MvPowerSeries.HasSubst (e Y) := hs (cc_e Y)
  have hsL : MvPowerSeries.HasSubst (l Y) := hs (cc_l Y)
  have key : ∀ g, MvPowerSeries.subst (e Y) (MvPowerSeries.subst (l Y) g) = g := fun g => by
    rw [MvPowerSeries.subst_comp_subst_apply hsL hsE]
    simp_rw [lgex Y]
    rw [MvPowerSeries.subst_self]
    rfl
  have h := congrArg (MvPowerSeries.subst (e Y)) (congrArg (MvPowerSeries.pderiv C k) (exlg Y n))
  rw [pderiv_subst hl k, ← MvPowerSeries.coe_substAlgHom hsE, map_sum] at h
  simp only [map_mul, MvPowerSeries.coe_substAlgHom, key] at h
  refine h.trans ?_
  by_cases hnk : n = k
  · subst hnk
    rw [MvPowerSeries.pderiv_X_self, if_pos rfl, ← MvPowerSeries.coe_substAlgHom hsE, map_one]
  · rw [MvPowerSeries.pderiv_X_of_ne hnk, if_neg hnk, ← MvPowerSeries.coe_substAlgHom hsE, map_zero]
end Formalism.L2.FormalSeriesBounds.VP
