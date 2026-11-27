-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ChG.chi_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:22:49.404672+00:00
-- url     : https://prove2.me/submissions/bbe7080d-ac0f-4811-9c55-cc262d88f126

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieChar
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MfactMulCoeffMvExpLinF
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffPderivUncurry
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_F
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_ev_id
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_eval_single_eq_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_singlePointUncurry
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2


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
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.L2.FormalSeriesBounds.ChG
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd)
open VP
namespace Formalism.L2.FormalSeriesBounds.ChG
theorem _root_.solution {χ : PS C 1 dd} (hχ : Y.IsChar χ) :
    MvPowerSeries.subst (fun k => Y.B.G.F k) (un1 χ) =
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd)) (un1 χ) *
        MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd)) (un1 χ) := by
  have h := hχ.2.2
  rw [eval_single_eq_subst, eval_single_eq_subst, eval_single_eq_subst] at h
  rw [subst_singlePointUncurry (cc_F Y), subst_singlePointUncurry (fun _ => cc_X _), subst_singlePointUncurry (fun _ => cc_X _)]
  have h2 : (fun p : Fin 1 × Fin dd => addOf Y.B.G.F (pt C dd 0) (pt C dd 1) p.2) =
      fun p : Fin 1 × Fin dd => Y.B.G.F p.2 := by
    funext p
    exact ev_id _
  rw [h2] at h
  exact h
end Formalism.L2.FormalSeriesBounds.ChG
