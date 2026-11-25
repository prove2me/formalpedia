-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.l_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:39:35.234443+00:00
-- url     : https://prove2.me/submissions/022c1656-7533-443c-bb44-f6b9c61b808d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PullbackLogCoordsEvalZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_ev_id
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_const
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_eval_single_eq_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_singlePointUncurry


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
theorem _root_.solution (m : Fin dd) :
    MvPowerSeries.subst (fun k => Y.B.G.F k) (l Y m) =
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd)) (l Y m) +
        MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd)) (l Y m) := by
  have hF : addOf Y.B.G.F (pt C dd 0) (pt C dd 1) = fun k => Y.B.G.F k :=
    funext fun k => ev_id (Y.B.G.F k)
  have h := Y.lg_add m
  rw [hF, eval_single_eq_subst, eval_single_eq_subst, eval_single_eq_subst] at h
  show MvPowerSeries.subst (fun k => Y.B.G.F k) (un1 (Y.lg m)) =
    MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd)) (un1 (Y.lg m)) +
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd)) (un1 (Y.lg m))
  rw [subst_singlePointUncurry (fun k => Y.B.G.const k), subst_singlePointUncurry (fun k => MvPowerSeries.constantCoeff_X _),
    subst_singlePointUncurry (fun k => MvPowerSeries.constantCoeff_X _)]
  exact h
end Formalism.L2.FormalSeriesBounds.VP
