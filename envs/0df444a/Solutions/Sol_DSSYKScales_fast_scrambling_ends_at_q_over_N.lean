-- Prove2me | solution 1 for DSSYKScales.fast_scrambling_ends_at_q_over_N
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:31:21.384104+00:00
-- url     : https://prove2.me/submissions/96cb16dd-afdd-4d22-8fd4-1b55a957b900

import Mathlib
import Definitions.Def_DSSYKScales_defs

open Filter Topology

namespace DSSYKScales

theorem aux_fsq_Qtop (N q : ℕ → ℕ) (lam : ℝ)
    (hlim : IsDoubleScaledLimit N q lam) :
    Tendsto (fun n => (q n : ℝ)) atTop atTop := by
  obtain ⟨hlam, hN, hq⟩ := hlim
  have h2 : Tendsto (fun n => ((q n : ℝ) ^ 2) / (N n : ℝ) * (N n : ℝ)) atTop atTop :=
    hq.pos_mul_atTop hlam hN
  have h3 : Tendsto (fun n => (q n : ℝ) ^ 2) atTop atTop := by
    refine h2.congr' ?_
    filter_upwards [hN.eventually_gt_atTop 0] with n hn
    field_simp
  rw [tendsto_atTop] at h3 ⊢
  intro b
  filter_upwards [h3 (max b 0 ^ 2)] with n hn
  have h0 : (0:ℝ) ≤ q n := Nat.cast_nonneg _
  by_contra h
  push Not at h
  have : (q n : ℝ) < max b 0 := lt_of_lt_of_le h (le_max_left _ _)
  nlinarith [le_max_right b 0]

theorem aux_fsq_upper (a : ℝ) : 1 - Real.exp (-a) ≤ a := by
  have := Real.add_one_le_exp (-a)
  linarith

theorem aux_fsq_lower (a : ℝ) (ha : 0 ≤ a) : a / (1 + a) ≤ 1 - Real.exp (-a) := by
  have h := Real.add_one_le_exp a
  have he : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
  have hp := Real.exp_pos (-a)
  rw [div_le_iff₀ (by linarith)]
  nlinarith

end DSSYKScales

open DSSYKScales

theorem solution (N q : ℕ → ℕ) (lam J : ℝ) (hJ : 0 < J)
    (hlim : IsDoubleScaledLimit N q lam) :
    Tendsto (fun n => (N n : ℝ) / (q n : ℝ) *
        scramblingProbability (N n) (q n) J (Real.log (q n : ℝ) / ((q n : ℝ) * J)))
      atTop (𝓝 (Real.log (1 + lam) / lam)) := by
  have hQ := aux_fsq_Qtop N q lam hlim
  obtain ⟨hlam, hN, hq⟩ := hlim
  let x : ℕ → ℝ := fun n => (q n : ℝ) / (N n : ℝ) *
    Real.exp (((q n : ℝ) - 1) * J * (Real.log (q n : ℝ) / ((q n : ℝ) * J)))
  have hx0 : ∀ n, 0 ≤ x n := fun n => by
    have : (0:ℝ) ≤ (q n : ℝ) / (N n : ℝ) := by positivity
    exact mul_nonneg this (Real.exp_pos _).le
  have hx : Tendsto x atTop (𝓝 lam) := by
    have h1 : Tendsto (fun n => ((q n : ℝ)) ^ (-(1:ℝ) / (q n : ℝ))) atTop (𝓝 1) :=
      tendsto_rpow_neg_div.comp hQ
    have h2 := hq.mul h1
    rw [mul_one] at h2
    refine h2.congr' ?_
    filter_upwards [hQ.eventually_gt_atTop 0, hN.eventually_gt_atTop 0] with n hQn hMn
    simp only [x]
    rw [Real.rpow_def_of_pos hQn]
    have : ((q n : ℝ) - 1) * J * (Real.log (q n : ℝ) / ((q n : ℝ) * J))
        = Real.log (q n : ℝ) + Real.log (q n : ℝ) * (-(1:ℝ) / (q n : ℝ)) := by
      field_simp
      ring
    rw [this, Real.exp_add, Real.exp_log hQn]
    field_simp
  let L : ℕ → ℝ := fun n => Real.log (1 + x n)
  have hL0 : ∀ n, 0 ≤ L n := fun n => Real.log_nonneg (by linarith [hx0 n])
  have hL : Tendsto L atTop (𝓝 (Real.log (1 + lam))) :=
    ((Real.continuousAt_log (by linarith : (1 + lam) ≠ 0)).tendsto).comp
      (tendsto_const_nhds.add hx)
  have hQ1 : Tendsto (fun n => (q n : ℝ) - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ hQ
  have hQ1inv : Tendsto (fun n => ((q n : ℝ) - 1)⁻¹) atTop (𝓝 0) := hQ1.inv_tendsto_atTop
  let a : ℕ → ℝ := fun n => L n / ((q n : ℝ) - 1)
  have ha : Tendsto a atTop (𝓝 0) := by
    have := hL.mul hQ1inv
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards with n
    simp only [a, div_eq_mul_inv]
  let A : ℕ → ℝ := fun n => (N n : ℝ) / (q n : ℝ) * a n
  have hA : Tendsto A atTop (𝓝 (Real.log (1 + lam) / lam)) := by
    have h1 : Tendsto (fun n => (((q n : ℝ) ^ 2) / (N n : ℝ))⁻¹) atTop (𝓝 lam⁻¹) :=
      hq.inv₀ hlam.ne'
    have h2 : Tendsto (fun n => 1 + ((q n : ℝ) - 1)⁻¹) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hQ1inv
    have h3 := (h1.mul h2).mul hL
    have hc : lam⁻¹ * (1 + 0) * Real.log (1 + lam) = Real.log (1 + lam) / lam := by
      rw [add_zero, mul_one, inv_mul_eq_div]
    rw [hc] at h3
    refine h3.congr' ?_
    filter_upwards [hQ.eventually_gt_atTop 1, hN.eventually_gt_atTop 0] with n hQn hMn
    simp only [A, a]
    have hq1 : (q n : ℝ) - 1 ≠ 0 := by linarith
    have hq0 : (q n : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  have hlow : Tendsto (fun n => A n / (1 + a n)) atTop (𝓝 (Real.log (1 + lam) / lam)) := by
    have := hA.div (tendsto_const_nhds.add ha) (by norm_num : (1:ℝ) + 0 ≠ 0)
    rw [add_zero, div_one] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hA ?_ ?_
  · filter_upwards [hQ.eventually_gt_atTop 1] with n hQn
    have ha0 : 0 ≤ a n := div_nonneg (hL0 n) (by linarith)
    have hMQ : (0:ℝ) ≤ (N n : ℝ) / (q n : ℝ) := by positivity
    have heq : scramblingProbability (N n) (q n) J (Real.log (q n : ℝ) / ((q n : ℝ) * J))
        = 1 - Real.exp (-a n) := by
      simp only [scramblingProbability]
      rw [Real.rpow_def_of_pos (by linarith [hx0 n] : (0:ℝ) < 1 + x n)]
      simp only [a, L]
      congr 2
      ring
    rw [heq]
    simp only [A]
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (aux_fsq_lower (a n) ha0) hMQ
  · filter_upwards [hQ.eventually_gt_atTop 1] with n hQn
    have hMQ : (0:ℝ) ≤ (N n : ℝ) / (q n : ℝ) := by positivity
    have heq : scramblingProbability (N n) (q n) J (Real.log (q n : ℝ) / ((q n : ℝ) * J))
        = 1 - Real.exp (-a n) := by
      simp only [scramblingProbability]
      rw [Real.rpow_def_of_pos (by linarith [hx0 n] : (0:ℝ) < 1 + x n)]
      simp only [a, L]
      congr 2
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left (aux_fsq_upper (a n)) hMQ
