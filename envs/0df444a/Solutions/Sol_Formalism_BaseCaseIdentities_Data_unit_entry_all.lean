-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.unit_entry_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:18:49.911284+00:00
-- url     : https://prove2.me/submissions/14ce2bae-dd86-4fbb-a973-5b9e6700a190

import Definitions.Def_Formalism_FrobeniusBaseCase_StatementFix
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseFalseGeneralHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_FixAll
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_qs_sigma_lt_one
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_e_real
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_q_cast
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_q_pos
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_v_l_inv
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_zvec_eq_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_coeff_sum_C_mul_X_pow


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
theorem _root_.solution : D.UnitEntryAll := by
  intro s hs1 hsK c hc P hP d hu h
  have h1 := h.1 c (by rw [hc]; exact hsK)
  rw [hc, D.zvec_eq_zero (by omega), zero_sub] at h1
  have h2 := h1 (Finsupp.single d (D.q ^ s))
  have hq0 : D.q ^ s ≠ 0 := pow_ne_zero _ (by have := D.q_pos; omega)
  have hcoef : coeff (Finsupp.single d (D.q ^ s)) (D.m s c)
      = ((-1) ^ s * ((D.l : k) ^ eNum D.l s)⁻¹) * P d := by
    rw [hP, coeff_C_mul, coeff_sum_C_mul_X_pow]
    simp only [Finsupp.single_left_inj hq0]
    rw [Finset.sum_ite_eq]
    simp
  have hvl : D.v (((D.l : k) ^ eNum D.l s)⁻¹) = ((-(eNum D.l s : ℝ) : ℝ) : WithTop ℝ) := by
    rw [← inv_pow]
    generalize eNum D.l s = e
    induction e with
    | zero => simp
    | succ e ih =>
      rw [pow_succ, AddValuation.map_mul, ih, D.v_l_inv, ← WithTop.coe_add]
      congr 1
      push_cast
      ring
  have hsign : D.v ((-1 : k) ^ s) = 0 := by
    rcases neg_one_pow_eq_or k s with h | h <;> rw [h] <;> simp [AddValuation.map_neg]
  rw [map_neg, AddValuation.map_neg, hcoef, AddValuation.map_mul, AddValuation.map_mul, hsign, hvl,
    hu, zero_add, add_zero, Finsupp.degree_single, ← WithTop.coe_add, WithTop.coe_le_coe] at h2
  have h3 := D.qs_sigma_lt_one s hsK
  have h4 := D.e_real s
  have h5 : ((D.q ^ s : ℕ) : ℝ) = qnum D.l ^ s := by
    rw [Nat.cast_pow, D.q_cast]
  rw [h5] at h2
  unfold Data.top Data.rad at h2
  nlinarith
end Formalism.BaseCaseIdentities.Data
