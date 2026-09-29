-- Prove2me | solution 1 for DSSYKScales.fast_scrambling_string_units
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:07:21.308553+00:00
-- url     : https://prove2.me/submissions/bd6d8818-3cc4-45e9-a113-321f792e6e57

import Mathlib
import Definitions.Def_DSSYKScales_defs

open Filter Topology

namespace DSSYKScales

theorem aux_fss_q_atTop (N q : ℕ → ℕ) (lam : ℝ) (hlim : IsDoubleScaledLimit N q lam) :
    Tendsto (fun n => (q n : ℝ)) atTop atTop := by
  obtain ⟨hlam, hN, hq⟩ := hlim
  have h2 : Tendsto (fun n => ((q n : ℝ) ^ 2) / (N n : ℝ) * (N n : ℝ)) atTop atTop :=
    hq.pos_mul_atTop hlam hN
  have h3 : Tendsto (fun n => ((q n : ℝ) ^ 2)) atTop atTop := by
    refine h2.congr' ?_
    filter_upwards [hN.eventually_gt_atTop 0] with n hn
    field_simp
  rw [tendsto_atTop] at h3 ⊢
  intro b
  filter_upwards [h3 ((max b 0) ^ 2)] with n hn
  have h0 : (0:ℝ) ≤ q n := Nat.cast_nonneg _
  have hb : b ≤ max b 0 := le_max_left _ _
  have hb0 : 0 ≤ max b 0 := le_max_right _ _
  nlinarith

theorem aux_fss_bounds (Nn a x : ℝ) (hN : 0 ≤ Nn) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    Nn * a * x * (1 + x)⁻¹ * Real.exp (-(a * x)) ≤
        Nn * (1 - Real.exp (-(a * Real.log (1 + x)))) ∧
    Nn * (1 - Real.exp (-(a * Real.log (1 + x)))) ≤ Nn * a * x := by
  have h1x : 0 < 1 + x := by linarith
  have hL1 : Real.log (1 + x) ≤ x := by
    have := Real.log_le_sub_one_of_pos h1x; linarith
  have hL2 : x * (1 + x)⁻¹ ≤ Real.log (1 + x) := by
    have := Real.one_sub_inv_le_log_of_pos h1x
    have e : 1 - (1 + x)⁻¹ = x * (1 + x)⁻¹ := by field_simp; ring
    linarith
  have hL0 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  have hy0 : 0 ≤ a * Real.log (1 + x) := mul_nonneg ha hL0
  have hup : 1 - Real.exp (-(a * Real.log (1 + x))) ≤ a * Real.log (1 + x) := by
    have := Real.add_one_le_exp (-(a * Real.log (1 + x))); linarith
  have hlow : (a * Real.log (1 + x)) * Real.exp (-(a * Real.log (1 + x))) ≤
      1 - Real.exp (-(a * Real.log (1 + x))) := by
    have h := Real.add_one_le_exp (a * Real.log (1 + x))
    have hpos := Real.exp_pos (-(a * Real.log (1 + x)))
    have : Real.exp (a * Real.log (1 + x)) * Real.exp (-(a * Real.log (1 + x))) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith
  have hyax : a * Real.log (1 + x) ≤ a * x := mul_le_mul_of_nonneg_left hL1 ha
  have hyax2 : a * (x * (1 + x)⁻¹) ≤ a * Real.log (1 + x) := mul_le_mul_of_nonneg_left hL2 ha
  constructor
  · have hexp : Real.exp (-(a * x)) ≤ Real.exp (-(a * Real.log (1 + x))) :=
      Real.exp_le_exp.mpr (by linarith)
    calc Nn * a * x * (1 + x)⁻¹ * Real.exp (-(a * x))
        = Nn * ((a * (x * (1 + x)⁻¹)) * Real.exp (-(a * x))) := by ring
      _ ≤ Nn * ((a * Real.log (1 + x)) * Real.exp (-(a * Real.log (1 + x)))) := by
          apply mul_le_mul_of_nonneg_left _ hN
          exact mul_le_mul hyax2 hexp (Real.exp_pos _).le hy0
      _ ≤ Nn * (1 - Real.exp (-(a * Real.log (1 + x)))) := mul_le_mul_of_nonneg_left hlow hN
  · calc Nn * (1 - Real.exp (-(a * Real.log (1 + x)))) ≤ Nn * (a * Real.log (1 + x)) :=
          mul_le_mul_of_nonneg_left hup hN
      _ ≤ Nn * (a * x) := mul_le_mul_of_nonneg_left hyax hN
      _ = Nn * a * x := by ring

theorem aux_fss_main (N q : ℕ → ℕ) (lam J : ℝ)
    (hlim : IsDoubleScaledLimit N q lam) (ts : ℝ) :
    Tendsto (fun n => (N n : ℝ) * scramblingProbability (N n) (q n) J (ts / (q n : ℝ)))
      atTop (𝓝 (Real.exp (J * ts))) := by
  have hqT := aux_fss_q_atTop N q lam hlim
  obtain ⟨hlam, hN, hq⟩ := hlim
  let E : ℕ → ℝ := fun n => ((q n : ℝ) - 1) * J * (ts / (q n : ℝ))
  let x : ℕ → ℝ := fun n => (q n : ℝ) / (N n : ℝ) * Real.exp (E n)
  let a : ℕ → ℝ := fun n => 1 / ((q n : ℝ) - 1)
  have hinvq : Tendsto (fun n => ((q n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hqT
  have hq1 : Tendsto (fun n => (q n : ℝ) - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ (-1) hqT
  have haT : Tendsto a atTop (𝓝 0) := by
    show Tendsto (fun n => 1 / ((q n : ℝ) - 1)) atTop (𝓝 0)
    simp only [one_div]
    exact tendsto_inv_atTop_zero.comp hq1
  have hET : Tendsto E atTop (𝓝 (J * ts)) := by
    have h : Tendsto (fun n => J * ts - J * ts * ((q n : ℝ))⁻¹) atTop
        (𝓝 (J * ts - J * ts * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hinvq)
    rw [mul_zero, sub_zero] at h
    refine h.congr' ?_
    filter_upwards [hqT.eventually_gt_atTop 0] with n hn
    simp only [E]
    field_simp
  have hqN : Tendsto (fun n => (q n : ℝ) / (N n : ℝ)) atTop (𝓝 0) := by
    have h : Tendsto (fun n => ((q n : ℝ) ^ 2) / (N n : ℝ) * ((q n : ℝ))⁻¹) atTop
        (𝓝 (lam * 0)) := hq.mul hinvq
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [hqT.eventually_gt_atTop 0] with n hn
    field_simp
  have hxT : Tendsto x atTop (𝓝 0) := by
    have h := hqN.mul ((Real.continuous_exp.tendsto _).comp hET)
    rw [zero_mul] at h
    exact h
  have huT : Tendsto (fun n => (N n : ℝ) * a n * x n) atTop (𝓝 (Real.exp (J * ts))) := by
    have h : Tendsto (fun n => (1 + ((q n : ℝ) - 1)⁻¹) * Real.exp (E n)) atTop
        (𝓝 ((1 + 0) * Real.exp (J * ts))) :=
      (tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp hq1)).mul
        ((Real.continuous_exp.tendsto _).comp hET)
    rw [add_zero, one_mul] at h
    refine h.congr' ?_
    filter_upwards [hqT.eventually_gt_atTop 1, hN.eventually_gt_atTop 0] with n hn hNn
    have : (q n : ℝ) - 1 ≠ 0 := by linarith
    simp only [a, x]
    field_simp
    ring
  have hlowT : Tendsto (fun n => (N n : ℝ) * a n * x n * (1 + x n)⁻¹ * Real.exp (-(a n * x n)))
      atTop (𝓝 (Real.exp (J * ts) * (1 + 0)⁻¹ * Real.exp (-(0 * 0)))) := by
    refine (huT.mul ((tendsto_const_nhds.add hxT).inv₀ (by norm_num))).mul ?_
    exact (Real.continuous_exp.tendsto _).comp ((haT.mul hxT).neg)
  have e : Real.exp (J * ts) * (1 + 0)⁻¹ * Real.exp (-(0 * 0)) = Real.exp (J * ts) := by simp
  rw [e] at hlowT
  have key : ∀ᶠ n in atTop, (N n : ℝ) * scramblingProbability (N n) (q n) J (ts / (q n : ℝ)) =
      (N n : ℝ) * (1 - Real.exp (-(a n * Real.log (1 + x n)))) ∧ 0 ≤ (N n : ℝ) ∧ 0 ≤ a n ∧
      0 ≤ x n := by
    filter_upwards [hqT.eventually_gt_atTop 1, hN.eventually_gt_atTop 0] with n hn hNn
    have hx0 : 0 ≤ x n := by
      simp only [x]; positivity
    have ha0 : 0 ≤ a n := by
      simp only [a]; exact div_nonneg zero_le_one (by linarith)
    refine ⟨?_, hNn.le, ha0, hx0⟩
    have h1x : 0 < 1 + x n := by linarith
    unfold scramblingProbability
    rw [Real.rpow_def_of_pos h1x]
    simp only [a, x, E]
    ring_nf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowT huT ?_ ?_
  · filter_upwards [key] with n hn
    rw [hn.1]
    exact (aux_fss_bounds _ _ _ hn.2.1 hn.2.2.1 hn.2.2.2).1
  · filter_upwards [key] with n hn
    rw [hn.1]
    exact (aux_fss_bounds _ _ _ hn.2.1 hn.2.2.1 hn.2.2.2).2

end DSSYKScales

open DSSYKScales
open Filter Topology

theorem solution (N q : ℕ → ℕ) (lam J : ℝ)
    (hlim : IsDoubleScaledLimit N q lam) (ts : ℝ) :
    Tendsto (fun n => (N n : ℝ) * scramblingProbability (N n) (q n) J (ts / (q n : ℝ)))
      atTop (𝓝 (Real.exp (J * ts))) :=
  aux_fss_main N q lam J hlim ts
