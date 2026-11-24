-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_esum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:34.770347+00:00
-- url     : https://prove2.me/submissions/bd8f3e23-1084-43b8-98a7-1de4e9bb7516

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPrimeB
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhpr_one_sub_exp_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (v0 V : ℕ) :
    ∑ v ∈ Ico v0 V, ((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2)) ≤
      20 * Real.exp (-((v0 : ℝ) / 4)) := by
  have hr0 : 0 < Real.exp (-(1/4:ℝ)) := Real.exp_pos _
  have hterm : ∀ v : ℕ, ((v:ℝ) + 1) * Real.exp (-((v:ℝ) / 2)) ≤ 4 * Real.exp (-(1/4:ℝ)) ^ v := by
    intro v
    have h1 := Real.add_one_le_exp ((v:ℝ) / 4)
    have hv : (0:ℝ) ≤ v := Nat.cast_nonneg v
    calc ((v:ℝ) + 1) * Real.exp (-((v:ℝ) / 2))
        ≤ (4 * Real.exp ((v:ℝ) / 4)) * Real.exp (-((v:ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = 4 * (Real.exp ((v:ℝ) / 4) * Real.exp (-((v:ℝ) / 2))) := by ring
      _ = 4 * Real.exp (-(1/4:ℝ)) ^ v := by
          rw [← Real.exp_add, ← Real.exp_nat_mul]
          congr 2
          ring
  have h15 : (1:ℝ) / 5 ≤ 1 - Real.exp (-(1/4:ℝ)) := by
    have h := dhpr_one_sub_exp_neg (show (0:ℝ) < 1/4 by norm_num)
    have e : (1/4:ℝ) / (1 + 1/4) = 1 / 5 := by norm_num
    rw [e] at h
    exact h
  have hgeo : ∑ v ∈ Ico v0 V, Real.exp (-(1/4:ℝ)) ^ v ≤ 5 * Real.exp (-(1/4:ℝ)) ^ v0 := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [pow_add]
    rw [← Finset.mul_sum, mul_comm (Real.exp (-(1/4:ℝ)) ^ v0)]
    have hG0 : 0 ≤ ∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k :=
      Finset.sum_nonneg (fun i _ => pow_nonneg hr0.le i)
    have h := geom_sum_mul (Real.exp (-(1/4:ℝ))) (V - v0)
    have hV : 0 ≤ Real.exp (-(1/4:ℝ)) ^ (V - v0) := pow_nonneg hr0.le _
    have hmul := mul_le_mul_of_nonneg_left h15 hG0
    have hle : ∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k ≤ 5 := by
      have e : (∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k) * (1 - Real.exp (-(1/4:ℝ))) =
          -((∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k) * (Real.exp (-(1/4:ℝ)) - 1)) := by ring
      rw [h] at e
      linarith
    exact mul_le_mul_of_nonneg_right hle (pow_nonneg hr0.le _)
  calc ∑ v ∈ Ico v0 V, ((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2))
      ≤ ∑ v ∈ Ico v0 V, 4 * Real.exp (-(1/4:ℝ)) ^ v := Finset.sum_le_sum (fun v _ => hterm v)
    _ = 4 * ∑ v ∈ Ico v0 V, Real.exp (-(1/4:ℝ)) ^ v := by rw [Finset.mul_sum]
    _ ≤ 4 * (5 * Real.exp (-(1/4:ℝ)) ^ v0) := mul_le_mul_of_nonneg_left hgeo (by norm_num)
    _ = 20 * Real.exp (-((v0 : ℝ) / 4)) := by
        rw [← Real.exp_nat_mul]
        have e : (v0:ℝ) * -(1/4) = -((v0:ℝ) / 4) := by ring
        rw [e]; ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
