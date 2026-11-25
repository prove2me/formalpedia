-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.m_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:59:41.226865+00:00
-- url     : https://prove2.me/submissions/15f3d343-0393-4655-8705-ec1d2e6ed55d

import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_CoeffFrobOfNotDvd
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_ChainI
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_q_pos
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_q_odd
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_m_succ
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_BaseCaseIdentities_frob_sum_X
import Theorems.Thm_Formalism_BaseCaseIdentities_identity_e


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
theorem _root_.solution (s : ℕ) (hs : s < D.K) :
    ∃ P : C → Z → k, (∀ c d, 0 ≤ D.v (P c d)) ∧ (∀ c, D.lev c ≠ s → ∀ d, P c d = 0) ∧
    ∀ c, D.m s c = MvPowerSeries.C ((-1) ^ s * ((D.l : k) ^ eNum D.l s)⁻¹) *
      ∑ d, MvPowerSeries.C (P c d) * X d ^ (D.q ^ s) := by
  have hl2 : 2 ≤ D.l := by have := D.l_ge; omega
  induction s with
  | zero =>
    refine ⟨fun c d => if D.ι d = c then 1 else 0, ?_, ?_, ?_⟩
    · intro c d
      show 0 ≤ D.v (if D.ι d = c then 1 else 0)
      split_ifs <;> simp
    · intro c hc d
      show (if D.ι d = c then (1 : k) else 0) = 0
      rw [if_neg]
      rintro rfl
      exact hc (D.ι_lev d)
    · intro c
      have h0 : eNum D.l 0 = 0 := (identity_e D.l 0 hl2).1
      rw [h0]
      show D.zvec c = _
      unfold zvec
      simp only [pow_zero, inv_one, mul_one, map_one, one_mul, pow_one]
      refine Finset.sum_congr rfl fun d _ => ?_
      split_ifs <;> simp
  | succ s ih =>
    obtain ⟨P, hP1, hP2, hP3⟩ := ih (by omega)
    refine ⟨fun b d => ∑ c, P c d ^ D.q * D.g c b, ?_, ?_, ?_⟩
    · intro b d
      apply AddValuation.map_le_sum
      intro c _
      rw [AddValuation.map_mul, AddValuation.map_pow]
      exact add_nonneg (nsmul_nonneg (hP1 c d) _) (D.g_int c b)
    · intro b hb d
      apply Finset.sum_eq_zero
      intro c _
      by_cases hc : D.lev c = s
      · rw [D.g_supp c (by rw [hc]; exact hs) b (by rw [hc]; exact hb), mul_zero]
      · rw [hP2 c hc d, zero_pow (by have := D.q_pos; omega), zero_mul]
    · intro b
      rw [m_succ]
      obtain ⟨κ, hκ⟩ : ∃ κ : k, κ = (-1) ^ s * ((D.l : k) ^ eNum D.l s)⁻¹ := ⟨_, rfl⟩
      rw [← hκ] at hP3
      have hfr : ∀ c, frob D.q (D.m s c) =
          ∑ d, MvPowerSeries.C ((κ * P c d) ^ D.q) * X d ^ (D.q * D.q ^ s) := by
        intro c
        rw [hP3 c, Finset.mul_sum]
        have : ∀ d, (MvPowerSeries.C κ * (MvPowerSeries.C (P c d) * X d ^ (D.q ^ s)) :
            MvPowerSeries Z k) = MvPowerSeries.C (κ * P c d) * X d ^ (D.q ^ s) := by
          intro d
          rw [map_mul, mul_assoc]
        simp only [this]
        exact frob_sum_X D.q_pos (Nat.one_le_pow _ _ D.q_pos) _
      have hκ' : -(D.l : k)⁻¹ * κ ^ D.q = (-1) ^ (s + 1) * ((D.l : k) ^ eNum D.l (s + 1))⁻¹ := by
        have he : eNum D.l (s + 1) = 1 + D.q * eNum D.l s := (identity_e D.l s hl2).2.1
        have hsign : ((-1 : k)) ^ (s * D.q) = (-1) ^ s := by
          rw [mul_comm, pow_mul, D.q_odd.neg_one_pow]
        rw [he, hκ, mul_pow, ← pow_mul, hsign, inv_pow, ← pow_mul, pow_succ, pow_add, pow_one,
          mul_inv, mul_comm (eNum D.l s) D.q]
        ring
      rw [← hκ']
      simp only [hfr, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [map_sum, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← pow_succ', mul_pow]
      simp only [map_mul, map_neg, map_pow]
      ring
end Formalism.BaseCaseIdentities.Data
