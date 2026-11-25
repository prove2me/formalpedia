-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.second_way_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:22:34.485003+00:00
-- url     : https://prove2.me/submissions/b71b7935-55c5-4a4b-bafb-cc1c6a5298ae

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseKOneHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_step
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_K_pos
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_iterate
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_zvec
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_zvec_eq_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
open Formalism.BaseCaseIdentities.Data
variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)
namespace Formalism.BaseCaseIdentities.Data
theorem _root_.solution : D.SecondWay := by
  have h1 : D.InWTo 1 D.zvec := by
    refine ⟨?_, ?_⟩
    · intro c hc
      have : D.lev c = 0 := by omega
      rw [this]
      show D.Wt D.top (D.zvec c - D.zvec c)
      rw [sub_self]
      exact HasWt.zero
    · intro c hc
      rw [D.zvec_eq_zero (by omega)]
      exact HasWt.zero
  refine ⟨h1, fun J t hJ1 hJK hnc ht => D.step J hJ1 hJK t hnc ht, ?_⟩
  have hK := D.K_pos
  have hit : ∀ n, D.InWTo (min (n + 1) D.K) ((D.Psi)^[n] D.zvec) := by
    intro n
    induction n with
    | zero =>
      rw [min_eq_left (by omega)]
      exact h1
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have h2 := D.step _ (by omega) (min_le_right _ _) _ (D.noConst_iterate D.noConst_zvec n) ih
      have h3 : min (min (n + 1) D.K + 1) D.K = min (n + 1 + 1) D.K := by omega
      rwa [h3] at h2
  intro n hn
  have h2 := hit n
  rwa [min_eq_right (by omega)] at h2
end Formalism.BaseCaseIdentities.Data
