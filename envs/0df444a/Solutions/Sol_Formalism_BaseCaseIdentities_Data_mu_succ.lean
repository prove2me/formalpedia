-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.mu_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:18:47.860039+00:00
-- url     : https://prove2.me/submissions/df1fff4f-9ead-4c62-97eb-59f8d55b8b40

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseKOneHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_main_eq_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_K_pos
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_m_eq_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_m_succ
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_q_pos
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_zvec_eq_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_frob_zero


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
theorem _root_.solution (J : ℕ) (hJ1 : 1 ≤ J) (hJK : J ≤ D.K) (b : C) :
    D.mu (min (J + 1) D.K) b = D.zvec b + ∑ c, D.main J c b := by
  have hK := D.K_pos
  by_cases hb0 : D.lev b = 0
  · have h1 : D.mu (min (J + 1) D.K) b = D.zvec b := by
      rw [mu, if_pos (by rw [hb0]; omega), hb0]
      rfl
    rw [h1, Finset.sum_eq_zero, add_zero]
    intro c _
    exact D.main_eq_zero J c b (by omega)
  · rw [D.zvec_eq_zero hb0, zero_add]
    by_cases hb : D.lev b < min (J + 1) D.K
    · obtain ⟨s, hs⟩ : ∃ s, D.lev b = s + 1 := ⟨D.lev b - 1, by omega⟩
      rw [mu, if_pos hb, hs, m_succ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : D.lev c = s
      · rw [main, if_pos ⟨by omega, by omega⟩, hc, map_mul]
        ring
      · rw [D.m_eq_zero (by omega) hc, frob_zero D.q_pos, zero_mul, mul_zero,
          D.main_eq_zero J c b (by omega)]
    · rw [mu, if_neg hb]
      symm
      apply Finset.sum_eq_zero
      intro c _
      unfold main
      split_ifs with h
      · rw [D.g_supp c h.2 b (by omega), mul_zero, map_zero, zero_mul]
      · rfl
end Formalism.BaseCaseIdentities.Data
