-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.wt_m
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:04:11.600966+00:00
-- url     : https://prove2.me/submissions/a82b792b-2f20-4e9e-8ac2-6fcf94d514ad

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_v_neg_l_inv
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_wt_zvec
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_m_succ
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_q_cast
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_q_rho
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_C_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_mono
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_mul_C
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_sum
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_C_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mono
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
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
variable {k : Type*} [Field k] {Z C : Type*}
open Formalism.BaseCaseIdentities.Data
variable [Fintype Z] [Fintype C] (D : Data k Z C)
namespace Formalism.BaseCaseIdentities.Data
theorem _root_.solution (s : ℕ) (c : C) : D.Wt (rho D.l + qnum D.l ^ s * sg D.l D.i) (D.m s c) := by
  induction s generalizing c with
  | zero =>
    rw [pow_zero, one_mul]
    exact D.wt_zvec c
  | succ s ih =>
    rw [m_succ]
    have h1 : ∀ c', D.Wt (0 + (D.q : ℝ) * (rho D.l + qnum D.l ^ s * sg D.l D.i))
        (frob D.q (D.m s c') * MvPowerSeries.C (D.g c' c)) := fun c' =>
      HasWt.mul_C (by simpa using D.g_int c' c) (HasWt.frob (ih c') D.q)
    have h2 := HasWt.C_mul (le_of_eq D.v_neg_l_inv.symm)
      (HasWt.sum Finset.univ (fun c' _ => h1 c'))
    refine HasWt.mono ?_ h2
    rw [D.q_cast, pow_succ]
    have := D.q_rho
    nlinarith
end Formalism.BaseCaseIdentities.Data
