-- Prove2me | solution 1 for ClauseBound.Part.Lower.step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:35:23.304852+00:00
-- url     : https://prove2.me/submissions/8f47d1fd-fd0a-473b-adf1-b2dfc4222f83

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Lower
import Theorems.Thm_ClauseBound_Part_Lower_ratio_ge
import Theorems.Thm_ClauseBound_Part_Lower_sum_v_ge
import Theorems.Thm_ClauseBound_Part_Lower_sum_k_ge
import Theorems.Thm_ClauseBound_Part_Lower_step_arith
import Theorems.Thm_ClauseBound_Part_Lower_cHR_sq
import Theorems.Thm_ClauseBound_Part_Lower_cHR_pos
import Theorems.Thm_ClauseBound_Part_mul_p_eq


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Lower
namespace ClauseBound.Part.Lower
theorem _root_.solution {H : ℝ} {B : ℕ} (hH : 0 ≤ H) (hB : (3890 : ℝ) ≤ B) {n : ℕ} (hn : 4 * (B : ℝ) / cHR + cHR ≤ Real.sqrt n)
    (ih : ∀ m, 1 ≤ m → m < n → H * Real.exp (cHR * Real.sqrt m) / (m : ℝ) ^ B ≤ p m) :
    H * Real.exp (cHR * Real.sqrt n) / (n : ℝ) ^ B ≤ p n := by
  have hZ := cHR_sq
  have hc : 0 < cHR := cHR_pos
  generalize cHR = c at *
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt n := ⟨_, rfl⟩
  rw [← hsdef] at hn ⊢
  have hs2 : s ^ 2 = n := by rw [hsdef, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hBc : 0 < 4 * (B : ℝ) / c := by positivity
  have hs0 : 0 < s := by linarith
  have hsc : c ≤ s := by linarith
  have hcs : 4 * (B : ℝ) ≤ c * s := by
    have : 4 * (B : ℝ) / c ≤ s := by linarith
    rw [div_le_iff₀ hc] at this
    linarith
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := by rw [← hs2]; positivity
    exact_mod_cast this
  obtain ⟨α, hα⟩ : ∃ α, α = c / (2 * s) - B / s ^ 2 := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = c / (2 * s ^ 3) := ⟨_, rfl⟩
  have hα0 : 0 < α := by
    have e : c / (2 * s) - B / s ^ 2 = (c * s - 2 * B) / (2 * s ^ 2) := by field_simp
    rw [hα, e]
    exact div_pos (by linarith) (by positivity)
  have hα1 : α ≤ 1 := by
    have h1 : c / (2 * s) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have h2 : 0 ≤ (B : ℝ) / s ^ 2 := by positivity
    linarith
  have hγ0 : 0 ≤ γ := by rw [hγ]; positivity
  have hγn : 1 ≤ γ * (s ^ 2) ^ 2 := by
    have e : γ * (s ^ 2) ^ 2 = c * s / 2 := by rw [hγ]; field_simp
    rw [e]
    linarith
  obtain ⟨K, hK⟩ : ∃ K, K = ⌈1 / α⌉₊ := ⟨_, rfl⟩
  have hw0 : 0 < 1 / α := by positivity
  have hK0 : 1 ≤ K := by rw [hK]; exact Nat.ceil_pos.2 hw0
  have hK1 : 1 / α ≤ K := by rw [hK]; exact Nat.le_ceil _
  have hK2 : (K : ℝ) ≤ 1 / α + 1 := by rw [hK]; exact (Nat.ceil_lt_add_one hw0.le).le
  obtain ⟨F, hF⟩ : ∃ F, F = Real.exp (c * s) / (s ^ 2) ^ B := ⟨_, rfl⟩
  have hF0 : 0 ≤ F := by rw [hF]; positivity
  -- one term
  have term : ∀ k v : ℕ, 1 ≤ k → 1 ≤ v →
      H * F * ((v : ℝ) * Real.exp (-(α * k * v)) * (1 - γ * (k : ℝ) ^ 2 * (v : ℝ) ^ 2)) ≤ if k * v < n then (v : ℝ) * p (n - k * v) else 0 := by
    intro k v hk hv
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = k * v := ⟨_, rfl⟩
    have e1 : α * k * v = α * x := by rw [hx]; ring
    have e2 : γ * (k : ℝ) ^ 2 * (v : ℝ) ^ 2 = γ * x ^ 2 := by rw [hx]; ring
    have hx0 : 0 ≤ x := by rw [hx]; positivity
    rw [e1, e2]
    split_ifs with h
    · have hxs : x < s ^ 2 := by rw [hs2, hx]; exact_mod_cast h
      have hr := ratio_ge B hc.le hs0 hx0 hxs
      rw [← hα, ← hγ, ← hF] at hr
      have hm : ((n - k * v : ℕ) : ℝ) = s ^ 2 - x := by rw [Nat.cast_sub h.le, hs2, hx]; push_cast; ring
      have hi := ih (n - k * v) (by omega) (Nat.sub_lt hn0 (Nat.mul_pos hk hv))
      rw [hm] at hi
      calc H * F * ((v : ℝ) * Real.exp (-(α * x)) * (1 - γ * x ^ 2)) = v * (H * (F * (Real.exp (-(α * x)) * (1 - γ * x ^ 2)))) := by ring
        _ ≤ v * (H * (Real.exp (c * Real.sqrt (s ^ 2 - x)) / (s ^ 2 - x) ^ B)) := by gcongr
        _ = v * (H * Real.exp (c * Real.sqrt (s ^ 2 - x)) / (s ^ 2 - x) ^ B) := by ring
        _ ≤ v * p (n - k * v) := by gcongr
    · have hxs : s ^ 2 ≤ x := by rw [hs2, hx]; exact_mod_cast not_lt.1 h
      have h1 : γ * (s ^ 2) ^ 2 ≤ γ * x ^ 2 := by gcongr
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith))
  -- the sum over v for one k
  have sumv : ∀ k ∈ Ioc 0 K, 1 / (α * k) ^ 2 - 1 / 4 - 486 * (γ * (k : ℝ) ^ 2) / (α * k) ^ 4
      ≤ ∑ v ∈ Icc 1 n, (v : ℝ) * Real.exp (-(α * k * v)) * (1 - γ * (k : ℝ) ^ 2 * (v : ℝ) ^ 2) := by
    intro k hk
    obtain ⟨hk0, hkK⟩ := Finset.mem_Ioc.1 hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
    have hkK' : (k : ℝ) ≤ K := by exact_mod_cast hkK
    refine sum_v_ge (by positivity) ?_ (by positivity) n ?_
    · calc α * k ≤ α * (1 / α + 1) := by gcongr; exact hkK'.trans hK2
        _ = 1 + α := by field_simp
        _ ≤ 2 := by linarith
    · rw [← hs2]
      have h1 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk1
      calc 1 ≤ γ * (s ^ 2) ^ 2 := hγn
        _ = γ * 1 * (s ^ 2) ^ 2 := by ring
        _ ≤ γ * (k : ℝ) ^ 2 * (s ^ 2) ^ 2 := by gcongr
  -- the recurrence
  have hrec : ((n : ℝ) * p n) = ∑ v ∈ Icc 1 n, ∑ k ∈ Icc 1 (n / v), (v : ℝ) * p (n - k * v) := by exact_mod_cast mul_p_eq n
  have hmain : H * F * s ^ 2 ≤ (n : ℝ) * p n := by
    calc H * F * s ^ 2 ≤ H * F * ∑ k ∈ Ioc 0 K, (1 / (α * k) ^ 2 - 1 / 4 - 486 * (γ * (k : ℝ) ^ 2) / (α * k) ^ 4) := by
          gcongr
          exact (step_arith hc hB hn hα hγ hZ hK1 hK2).trans (sum_k_ge hα0 hγ0 hK0)
      _ ≤ H * F * ∑ k ∈ Ioc 0 K, ∑ v ∈ Icc 1 n, (v : ℝ) * Real.exp (-(α * k * v)) * (1 - γ * (k : ℝ) ^ 2 * (v : ℝ) ^ 2) := by
          gcongr with k hk
          exact sumv k hk
      _ = ∑ k ∈ Ioc 0 K, ∑ v ∈ Icc 1 n, H * F * ((v : ℝ) * Real.exp (-(α * k * v)) * (1 - γ * (k : ℝ) ^ 2 * (v : ℝ) ^ 2)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
      _ ≤ ∑ k ∈ Ioc 0 K, ∑ v ∈ Icc 1 n, if k * v < n then (v : ℝ) * p (n - k * v) else 0 :=
          Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun v hv => term k v (Finset.mem_Ioc.1 hk).1 (Finset.mem_Icc.1 hv).1
      _ = ∑ v ∈ Icc 1 n, ∑ k ∈ Ioc 0 K, if k * v < n then (v : ℝ) * p (n - k * v) else 0 := Finset.sum_comm
      _ ≤ ∑ v ∈ Icc 1 n, ∑ k ∈ Icc 1 (n / v), (v : ℝ) * p (n - k * v) := by
          refine Finset.sum_le_sum fun v hv => ?_
          rw [← Finset.sum_filter]
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun _ _ _ => by positivity
          obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
          exact Finset.mem_Icc.2 ⟨(Finset.mem_Ioc.1 hk1).1, (Nat.le_div_iff_mul_le (Finset.mem_Icc.1 hv).1).2 hk2.le⟩
      _ = (n : ℝ) * p n := hrec.symm
  rw [← hs2, mul_div_assoc, ← hF]
  rw [← hs2, mul_comm (s ^ 2)] at hmain
  exact le_of_mul_le_mul_right hmain (by positivity)
end ClauseBound.Part.Lower
