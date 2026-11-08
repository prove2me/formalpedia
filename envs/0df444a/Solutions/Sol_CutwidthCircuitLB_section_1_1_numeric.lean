-- Prove2me | solution 1 for CutwidthCircuitLB.section_1_1_numeric
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:36:29.720205+00:00
-- url     : https://prove2.me/submissions/65cf54f8-c370-4982-b663-c3da5ce92c20

import Mathlib
import Definitions.Def_CutwidthCircuitLB_kappaE

namespace Aux_Cutwidth_numeric
open Finset

noncomputable def tm (x : ℝ) (i : ℕ) : ℝ := x ^ (2 * i) / ((2 * i).factorial : ℝ)

theorem tm_anti (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Antitone (tm x) := by
  apply antitone_nat_of_succ_le
  intro n
  unfold tm
  have hf : ((2 * (n + 1)).factorial : ℝ) = ((2 * n + 2) * (2 * n + 1)) * ((2 * n).factorial : ℝ) := by
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have hp : x ^ (2 * (n + 1)) = x ^ (2 * n) * x ^ 2 := by ring
  rw [hf, hp]
  have hpos : (0 : ℝ) < ((2 * n).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hxn : 0 ≤ x ^ (2 * n) := pow_nonneg h0 _
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  rw [div_le_div_iff₀ (by positivity) hpos]
  have : x ^ (2 * n) * x ^ 2 ≤ x ^ (2 * n) * ((2 * n + 2) * (2 * n + 1)) := by
    apply mul_le_mul_of_nonneg_left _ hxn
    have : (1 : ℝ) ≤ (2 * n + 2) * (2 * n + 1) := by nlinarith
    linarith
  nlinarith

theorem tends (x : ℝ) :
    Filter.Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * tm x i) Filter.atTop
      (nhds (Real.cos x)) := by
  have := (Real.hasSum_cos x).tendsto_sum_nat
  convert this using 2 with n
  apply Finset.sum_congr rfl
  intro i _
  unfold tm; ring

theorem cos_upper (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.cos x ≤ ∑ i ∈ range (2 * 3 + 1), (-1 : ℝ) ^ i * tm x i :=
  (tm_anti x h0 h1).tendsto_le_alternating_series (tends x) 3

theorem cos_lower (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    ∑ i ∈ range (2 * 3), (-1 : ℝ) ^ i * tm x i ≤ Real.cos x :=
  (tm_anti x h0 h1).alternating_series_le_tendsto (tends x) 3

end Aux_Cutwidth_numeric

open CutwidthCircuitLB Aux_Cutwidth_numeric in
theorem solution :
    (4.5624 : ℝ) < 1 + 1 / (2 * kappaE) ∧
      |1 + 1 / (2 * kappaE) - 4.5624977| < (5e-8 : ℝ) := by
  have hs1 : (1.41421356237 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs2 : Real.sqrt 2 < (1.41421356238 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  set c : ℝ := (1 + 2 * Real.sqrt 2) / 4 with hc
  have hc1 : -1 ≤ c := by rw [hc]; linarith
  have hc2 : c ≤ 1 := by rw [hc]; linarith
  set θ := Real.arccos c with hθ
  have hcosθ : Real.cos θ = c := Real.cos_arccos hc1 hc2
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg c
  have hθπ : θ ≤ Real.pi := Real.arccos_le_pi c
  have hcu : Real.cos (0.2939503814 : ℝ) < c := by
    have := cos_upper (0.2939503814 : ℝ) (by norm_num) (by norm_num)
    simp only [tm, Finset.sum_range_succ, Finset.sum_range_zero] at this
    norm_num [Nat.factorial] at this
    rw [hc]; linarith
  have hcl : c < Real.cos (0.29395038 : ℝ) := by
    have := cos_lower (0.29395038 : ℝ) (by norm_num) (by norm_num)
    simp only [tm, Finset.sum_range_succ, Finset.sum_range_zero] at this
    norm_num [Nat.factorial] at this
    rw [hc]; linarith
  have hθ2 : θ < 0.2939503814 := by
    by_contra h; push_neg at h
    have := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num) hθπ h
    linarith
  have hθ1 : 0.29395038 < θ := by
    by_contra h; push_neg at h
    have := Real.cos_le_cos_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_gt_three]) h
    linarith
  have hπ1 := Real.pi_gt_d20
  have hπ2 := Real.pi_lt_d20
  have hθpos : 0 < θ := by linarith
  have hv : 1 + 1 / (2 * kappaE) = 1 + Real.pi / (3 * θ) := by
    unfold kappaE
    rw [← hc, ← hθ]
    have : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [hv]
  have hlo : (3.14159265358979323846 : ℝ) / (3 * 0.2939503814) < Real.pi / (3 * θ) := by
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
    have := mul_lt_mul'' hπ1 hθ2 (by norm_num) hθ0
    linarith
  have hhi : Real.pi / (3 * θ) < (3.14159265358979323847 : ℝ) / (3 * 0.29395038) := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    have := mul_lt_mul'' hπ2 hθ1 (by linarith) (by norm_num)
    linarith
  refine ⟨?_, ?_⟩
  · have : (4.5624 : ℝ) < 1 + (3.14159265358979323846 : ℝ) / (3 * 0.2939503814) := by norm_num
    linarith
  · rw [abs_sub_lt_iff]
    have h1 : 1 + (3.14159265358979323847 : ℝ) / (3 * 0.29395038) - 4.5624977 < 5e-8 := by norm_num
    have h2 : 4.5624977 - (1 + (3.14159265358979323846 : ℝ) / (3 * 0.2939503814)) < 5e-8 := by norm_num
    constructor <;> linarith
