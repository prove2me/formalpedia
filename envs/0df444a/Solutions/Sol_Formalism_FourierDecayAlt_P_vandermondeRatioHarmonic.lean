-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.vandermondeRatioHarmonic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:53:49.101939+00:00
-- url     : https://prove2.me/submissions/63fae727-082a-4a8e-bccb-37c9c5eff2d4

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_log_one_add_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_pair_eq_NF
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_harm_eq_NF
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_NF_bd
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_sum_inv_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_xx_bd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.Sz Sz3
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Sz.HarmonicVand := by
  intro J de hJ hde
  have hfac : ∀ i i' : ℕ, i < i' → 0 < 1 + xx de i i' := by
    intro i i' h
    have := abs_le.mp (xx_bd de hde i i' h).1
    linarith [this.1]
  have hR : Rde J de = ∏ i ∈ Icc 1 J, ∏ i' ∈ Ioc i J, (1 + xx de i i') := rfl
  have hpos : 0 < Rde J de := by
    rw [hR]
    apply Finset.prod_pos; intro i _
    apply Finset.prod_pos; intro i' hi'
    exact hfac i i' (mem_Ioc.mp hi').1
  have hlog : Real.log (Rde J de) = ∑ i ∈ Icc 1 J, ∑ i' ∈ Ioc i J, Real.log (1 + xx de i i') := by
    rw [hR, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro i _
      rw [Real.log_prod]
      intro i' hi'
      exact (hfac i i' (mem_Ioc.mp hi').1).ne'
    · intro i _
      apply ne_of_gt
      apply Finset.prod_pos; intro i' hi'
      exact hfac i i' (mem_Ioc.mp hi').1
  have hM : ∑ i ∈ Icc 1 J, ∑ i' ∈ Ioc i J, xx de i i' = (1 / 4) * NF J de := pair_eq_NF J de
  have hE : |Real.log (Rde J de) - (1 / 4) * NF J de| ≤ Real.pi ^ 2 / 144 * J := by
    rw [hlog, ← hM, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ i ∈ Icc 1 J, |∑ i' ∈ Ioc i J, Real.log (1 + xx de i i') - ∑ i' ∈ Ioc i J, xx de i i'| ≤
        Real.pi ^ 2 / 144 := by
      intro i _
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have h1 : ∑ i' ∈ Ioc i J, |Real.log (1 + xx de i i') - xx de i i'| ≤
          ∑ i' ∈ Ioc i J, 1 / 24 * (1 / (((i' - i : ℕ) : ℝ)) ^ 2) := by
        apply Finset.sum_le_sum
        intro i' hi'
        have hb := xx_bd de hde i i' (mem_Ioc.mp hi').1
        have := log_one_add_sub _ hb.1
        linarith [hb.2]
      have h2 : ∑ i' ∈ Ioc i J, 1 / 24 * (1 / (((i' - i : ℕ) : ℝ)) ^ 2) =
          1 / 24 * ∑ d ∈ Icc 1 (J - i), 1 / (d : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_nbij' (fun i' => i' - i) (fun d => i + d)
        · intro a ha; simp only [mem_Ioc, mem_Icc] at *; omega
        · intro a ha; simp only [mem_Ioc, mem_Icc] at *; omega
        · intro a ha; simp only [mem_Ioc] at *; omega
        · intro a ha; simp only [mem_Icc] at *; omega
        · intro a ha; rfl
      have h3 := sum_inv_sq (J - i)
      linarith
    have h4 := Finset.sum_le_sum this
    simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel] at h4
    linarith
  refine ⟨hpos, ?_, ?_⟩
  · rw [harm_eq_NF]; exact hE
  · have hN := NF_bd J hJ de hde
    have hpi : Real.pi ^ 2 ≤ 10.8 := by
      have h1 := Real.pi_lt_d2
      have h0 := Real.pi_pos
      nlinarith
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    have hE' := abs_le.mp hE
    have hN' := abs_le.mp hN
    have hpJ : Real.pi ^ 2 / 144 * J ≤ 10.8 / 144 * J := by
      apply mul_le_mul_of_nonneg_right _ hJ0
      linarith
    rw [abs_le]
    constructor <;> linarith [hE'.1, hE'.2, hN'.1, hN'.2]
end Formalism.FourierDecayAlt.P
