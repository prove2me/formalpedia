-- Prove2me | solution 1 for ClauseBound.Part.p_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:29:53.257299+00:00
-- url     : https://prove2.me/submissions/8a6e949a-1ab3-4610-b298-87de7e3f220c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Upper
import Theorems.Thm_ClauseBound_Part_Upper_cHR_pos
import Theorems.Thm_ClauseBound_Part_Upper_cHR_sq
import Theorems.Thm_ClauseBound_Part_Upper_sqrt_sub_le
import Theorems.Thm_ClauseBound_Part_Upper_sum_mul_exp_le
import Theorems.Thm_ClauseBound_Part_Upper_sum_inv_sq_le
import Theorems.Thm_ClauseBound_Part_mul_p_eq
import Theorems.Thm_ClauseBound_Part_p_zero


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open Upper
namespace ClauseBound.Part
theorem _root_.solution (E : ℕ) : (p E : ℝ) ≤ Real.exp (cHR * Real.sqrt E) := by
  induction E using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [p_zero]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc := cHR_pos
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt n := ⟨_, rfl⟩
  have hs0 : 0 < s := hs ▸ Real.sqrt_pos.2 hn'
  have hss : s ^ 2 = n := hs ▸ Real.sq_sqrt hn'.le
  obtain ⟨a, ha⟩ : ∃ a, a = cHR / (2 * s) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  rw [← hs]
  have hterm : ∀ v ∈ Icc 1 n, ∀ k ∈ Icc 1 (n / v),
      (v : ℝ) * (p (n - k * v) : ℝ) ≤ Real.exp (cHR * s) * ((v : ℝ) * Real.exp (-(a * k * v))) := by
    intro v hv k hk
    have hv1 : 1 ≤ v := (mem_Icc.1 hv).1
    have hk1 : 1 ≤ k := (mem_Icc.1 hk).1
    have hkv : k * v ≤ n := (Nat.le_div_iff_mul_le hv1).1 (mem_Icc.1 hk).2
    have hpos : 0 < k * v := Nat.mul_pos hk1 hv1
    have h1 := ih (n - k * v) (by omega)
    have h2 : Real.sqrt ((n - k * v : ℕ) : ℝ) ≤ s - (k * v : ℝ) / (2 * s) := by
      rw [Nat.cast_sub hkv, hs]
      push_cast
      exact sqrt_sub_le hn' (by exact_mod_cast hkv)
    have h3 : Real.exp (cHR * Real.sqrt ((n - k * v : ℕ) : ℝ)) ≤ Real.exp (cHR * s) * Real.exp (-(a * k * v)) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      calc cHR * Real.sqrt ((n - k * v : ℕ) : ℝ) ≤ cHR * (s - (k * v : ℝ) / (2 * s)) := by gcongr
        _ = cHR * s + -(a * k * v) := by rw [ha]; ring
    calc (v : ℝ) * (p (n - k * v) : ℝ) ≤ v * (Real.exp (cHR * s) * Real.exp (-(a * k * v))) := by gcongr; exact h1.trans h3
      _ = Real.exp (cHR * s) * ((v : ℝ) * Real.exp (-(a * k * v))) := by ring
  have hsum : (n : ℝ) * p n ≤ n * Real.exp (cHR * s) := by
    calc (n : ℝ) * p n = ((n * p n : ℕ) : ℝ) := by push_cast; ring
      _ = ∑ v ∈ Icc 1 n, ∑ k ∈ Icc 1 (n / v), (v : ℝ) * (p (n - k * v) : ℝ) := by rw [mul_p_eq]; push_cast; rfl
      _ ≤ ∑ v ∈ Icc 1 n, ∑ k ∈ Icc 1 (n / v), Real.exp (cHR * s) * ((v : ℝ) * Real.exp (-(a * k * v))) :=
          sum_le_sum fun v hv => sum_le_sum (hterm v hv)
      _ ≤ ∑ v ∈ Icc 1 n, ∑ k ∈ Icc 1 n, Real.exp (cHR * s) * ((v : ℝ) * Real.exp (-(a * k * v))) :=
          sum_le_sum fun v _ => sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.div_le_self _ _)) fun _ _ _ => by positivity
      _ = Real.exp (cHR * s) * ∑ k ∈ Icc 1 n, ∑ v ∈ Icc 1 n, (v : ℝ) * Real.exp (-(a * k * v)) := by
          rw [sum_comm]
          simp only [mul_sum]
      _ ≤ Real.exp (cHR * s) * ∑ k ∈ Icc 1 n, 1 / (a * k) ^ 2 := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun k hk => ?_) (Real.exp_pos _).le
          have hk0 : (0 : ℝ) < k := by exact_mod_cast (mem_Icc.1 hk).1
          exact sum_mul_exp_le (by positivity) _
      _ = Real.exp (cHR * s) * (1 / a ^ 2 * ∑ k ∈ Icc 1 n, 1 / (k : ℝ) ^ 2) := by
          congr 1
          rw [mul_sum]
          exact sum_congr rfl fun k _ => by rw [mul_pow, one_div_mul_one_div]
      _ ≤ Real.exp (cHR * s) * (1 / a ^ 2 * (Real.pi ^ 2 / 6)) := by
          gcongr
          exact sum_inv_sq_le _
      _ = n * Real.exp (cHR * s) := by
          have hpi := Real.pi_pos
          rw [ha, div_pow, mul_pow, cHR_sq, hss]
          field_simp
          ring
  exact le_of_mul_le_mul_left hsum hn'
end ClauseBound.Part
