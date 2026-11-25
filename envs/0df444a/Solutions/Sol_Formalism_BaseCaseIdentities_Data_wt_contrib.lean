-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.wt_contrib
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:50:27.871881+00:00
-- url     : https://prove2.me/submissions/52689bb6-84a5-4b99-bd43-3ae1904359cf

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseKOneHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_rho_le_top
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_wt_two
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_wt_m_rho
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_C_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_add
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_mono
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_C_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mono
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_num_c
import Theorems.Thm_Formalism_BaseCaseIdentities_num_d
import Theorems.Thm_Formalism_BaseCaseIdentities_num_good


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
theorem _root_.solution (J : ℕ) (hJK : J ≤ D.K) (t : C → MvPowerSeries Z k)
    (ht : ∀ c, D.Wt D.top (t c - D.mu J c)) (N : ℕ) (hN : 2 ≤ N) (c b : C) :
    D.Wt D.top
      (∑ j ∈ Finset.Icc 1 N, MvPowerSeries.C (D.al c j b) * t c ^ (D.l ^ j) + D.main J c b) := by
  have hl := D.l_ge
  by_cases hcJ : D.lev c < J
  · have hcK : D.lev c < D.K := by omega
    have hgood := D.pure_good c hcK
    have hν : D.Wt D.top (t c - D.m (D.lev c) c) := by
      have := ht c
      rwa [mu, if_pos hcJ] at this
    have ht' : D.Wt (rho D.l) (t c) := by
      have h1 := HasWt.add (D.wt_m_rho (D.lev c) c) (HasWt.mono D.rho_le_top hν)
      rwa [add_sub_cancel] at h1
    have h2mem : 2 ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨by norm_num, hN⟩
    rw [← Finset.add_sum_erase _ _ h2mem, add_right_comm]
    refine HasWt.add (D.wt_two J hJK c b hcJ (t c) hν) ?_
    apply HasWt.sum
    intro j hj
    have hj' : j ≠ 2 ∧ 1 ≤ j ∧ j ≤ N := by
      simpa [Finset.mem_erase, Finset.mem_Icc] using hj
    by_cases hj1 : j = 1
    · subst hj1
      rw [D.al_one c hgood b, map_zero, zero_mul]
      exact HasWt.zero
    · have hj3 : 3 ≤ j := by omega
      refine HasWt.mono ?_ (HasWt.C_mul (D.al_good c hgood j b (by omega))
        (HasWt.pow ht' (D.l ^ j)))
      have := num_c hl hj3
      unfold top
      push_cast
      exact this
  · have ht' : D.Wt D.top (t c) := by
      have := ht c
      rwa [mu, if_neg hcJ, sub_zero] at this
    rw [main, if_neg (fun h => hcJ h.1), add_zero]
    apply HasWt.sum
    intro j hj
    have hj' : 1 ≤ j ∧ j ≤ N := by simpa [Finset.mem_Icc] using hj
    by_cases hg : D.good c
    · by_cases hj1 : j = 1
      · subst hj1
        rw [D.al_one c hg b, map_zero, zero_mul]
        exact HasWt.zero
      · refine HasWt.mono ?_ (HasWt.C_mul (D.al_good c hg j b (by omega))
          (HasWt.pow ht' (D.l ^ j)))
        have := num_good hl (j := j) (by omega)
        unfold top
        push_cast
        exact this
    · refine HasWt.mono ?_ (HasWt.C_mul (D.al_all c j b) (HasWt.pow ht' (D.l ^ j)))
      have := num_d hl (j := j) hj'.1
      unfold top
      push_cast
      exact this
end Formalism.BaseCaseIdentities.Data
