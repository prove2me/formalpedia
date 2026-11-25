-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.SelfConjPoints.rescale_HH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:16:18.492368+00:00
-- url     : https://prove2.me/submissions/f2824a7f-4ce8-4d7d-91e2-0e248d93e9db

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RescaleInV
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjPoints_inV_cc
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_SelfConjPoints_rescale_inV
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_InL_rescale


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
open Formalism.L2.FormalSeriesBounds.SelfConjPoints
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
namespace Formalism.L2.FormalSeriesBounds.SelfConjPoints
theorem _root_.solution (X : RawChart C d I κ) (x z : κ → PowerSeries C) (hx : ∀ i, PowerSeries.constantCoeff (x i) = 0)
    (hz : ∀ i, PowerSeries.constantCoeff (z i) = 0) (w : Fin 2 → C) :
    MvPowerSeries.rescale w (HH X x z) = HH X (rc (w 0) x) (rc (w 1) z) := by
  have hP : MvPowerSeries.HasSubst (pairSubst (fun i => inV 0 (x i)) (fun i => inV 1 (z i))) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ?_
    unfold pairSubst
    split_ifs
    · exact inV_cc 0 (hx q.2)
    · exact inV_cc 1 (hz q.2)
  have hw : MvPowerSeries.HasSubst (w • MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) C) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  unfold HH hAt
  rw [MvPowerSeries.rescale_eq_subst, MvPowerSeries.subst_comp_subst_apply hP hw]
  congr 1
  funext q
  rw [← MvPowerSeries.rescale_eq_subst]
  unfold pairSubst rc
  split_ifs
  · exact rescale_inV w 0 (x q.2)
  · exact rescale_inV w 1 (z q.2)
end Formalism.L2.FormalSeriesBounds.SelfConjPoints
