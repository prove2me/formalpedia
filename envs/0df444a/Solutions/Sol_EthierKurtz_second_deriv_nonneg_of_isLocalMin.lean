-- Prove2me | solution 1 for EthierKurtz.second_deriv_nonneg_of_isLocalMin
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T18:57:49.369641+00:00
-- url     : https://prove2.me/submissions/bbd36280-b750-4fcc-a675-ebc8e0ea2c80

import Mathlib

open scoped Topology

theorem solution
    {g : ℝ → ℝ}
    (hdiff : Differentiable ℝ g)
    (hg2 : DifferentiableAt ℝ (deriv g) 0)
    (hmin : IsLocalMin g 0) :
    0 ≤ deriv (deriv g) 0 := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, 0 < r := ⟨1, one_pos⟩
  have hdiffBall : DifferentiableOn ℝ g (Metric.ball 0 r) :=
    hdiff.differentiableOn
  by_contra hneg
  push Not at hneg
  have hderiv0 : deriv g 0 = 0 := hmin.deriv_eq_zero
  have hder : HasDerivAt (deriv g) (deriv (deriv g) 0) 0 :=
    hasDerivAt_deriv_iff.mpr hg2
  have hS := hder.tendsto_slope_zero_right
  have hL2 : deriv (deriv g) 0 < deriv (deriv g) 0 / 2 := by linarith
  have E : ∀ᶠ u in 𝓝[>] (0:ℝ),
      u⁻¹ • (deriv g (0 + u) - deriv g 0) < deriv (deriv g) 0 / 2 :=
    hS.eventually_lt_const hL2
  have E1 : ∀ᶠ u in 𝓝[>] (0:ℝ), deriv g u < 0 := by
    filter_upwards [E, self_mem_nhdsWithin] with u hu hpos
    have hu2 : u⁻¹ • (deriv g (0 + u) - deriv g 0)
        < deriv (deriv g) 0 / 2 := hu
    rw [Set.mem_Ioi] at hpos
    simp only [zero_add] at hu2
    rw [smul_eq_mul, hderiv0, sub_zero] at hu2
    have hu := hu2
    have h3 : deriv g u = u * (u⁻¹ * deriv g u) := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul]
    rw [h3]
    have h4 : u * (u⁻¹ * deriv g u) < u * (deriv (deriv g) 0 / 2) :=
      mul_lt_mul_of_pos_left hu hpos
    have h5 : u * (deriv (deriv g) 0 / 2) < 0 := by
      have hneg2 : deriv (deriv g) 0 / 2 < 0 := by linarith
      exact mul_neg_of_pos_of_neg hpos hneg2
    exact lt_trans h4 h5
  rw [eventually_nhdsWithin_iff] at E1
  have E1mem : {u : ℝ | 0 < u → deriv g u < 0} ∈ 𝓝 (0:ℝ) := E1
  obtain ⟨ε₁, hε₁, hsub⟩ := Metric.mem_nhds_iff.mp E1mem
  have hminmem : {x : ℝ | g 0 ≤ g x} ∈ 𝓝 (0:ℝ) := hmin
  obtain ⟨ε₂, hε₂, hsub2⟩ := Metric.mem_nhds_iff.mp hminmem
  set m := min (min ε₁ ε₂) (min r 1) / 2 with hmdef
  have hmpos : 0 < m := by
    rw [hmdef]
    have h1 : 0 < min (min ε₁ ε₂) (min r 1) :=
      lt_min (lt_min hε₁ hε₂) (lt_min hr one_pos)
    linarith
  have hmle : m ≤ min (min ε₁ ε₂) (min r 1) := by
    rw [hmdef]
    have h1 : 0 < min (min ε₁ ε₂) (min r 1) :=
      lt_min (lt_min hε₁ hε₂) (lt_min hr one_pos)
    linarith
  have hmlt : m < min (min ε₁ ε₂) (min r 1) := by
    rw [hmdef]
    have h1 : 0 < min (min ε₁ ε₂) (min r 1) :=
      lt_min (lt_min hε₁ hε₂) (lt_min hr one_pos)
    linarith
  have hm1 : m < ε₁ :=
    lt_of_lt_of_le hmlt (le_trans (min_le_left _ _) (min_le_left _ _))
  have hmr : m < r :=
    lt_of_lt_of_le hmlt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hm2 : m < ε₂ :=
    lt_of_lt_of_le hmlt (le_trans (min_le_left _ _) (min_le_right _ _))
  have hmball2 : m ∈ Metric.ball 0 ε₂ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hmpos]
    exact hm2
  have hmmin : g 0 ≤ g m := hsub2 hmball2
  have hcont : ContinuousOn g (Set.Icc 0 m) := by
    refine DifferentiableOn.continuousOn (hdiffBall.mono ?_)
    intro x hx
    have hx1 : 0 ≤ x := hx.1
    have hx2 : x ≤ m := hx.2
    have hxb : x ∈ Metric.ball 0 r := by
      rw [Metric.mem_ball, Real.dist_eq]
      have habs : |x - 0| = x := by rw [sub_zero, abs_of_nonneg hx1]
      rw [habs]
      exact lt_of_le_of_lt hx2 hmr
    exact hxb
  have hdiffIO : DifferentiableOn ℝ g (Set.Ioo 0 m) :=
    hdiffBall.mono (fun x hx => by
      have hx1 : 0 < x := hx.1
      have hx2 : x < m := hx.2
      have hxb : x ∈ Metric.ball 0 r := by
        rw [Metric.mem_ball, Real.dist_eq]
        have habs : |x - 0| = x := by
          rw [sub_zero, abs_of_nonneg (le_of_lt hx1)]
        rw [habs]
        exact lt_trans hx2 hmr
      exact hxb)
  obtain ⟨ξ, hξmem, hξeq⟩ := exists_deriv_eq_slope g hmpos hcont hdiffIO
  have hξball : ξ ∈ Metric.ball 0 ε₁ := by
    rw [Metric.mem_ball, Real.dist_eq]
    have habs : |ξ - 0| = ξ := by
      rw [sub_zero, abs_of_nonneg (le_of_lt hξmem.1)]
    rw [habs]
    exact lt_of_lt_of_le hξmem.2 (le_of_lt hm1)
  have hξneg : deriv g ξ < 0 := hsub hξball hξmem.1
  have hmul : g m - g 0 = deriv g ξ * m := by
    have h := hξeq
    rw [sub_zero] at h
    rw [h]
    exact (div_mul_cancel₀ _ (ne_of_gt hmpos)).symm
  have hlt : g m - g 0 < 0 := by
    rw [hmul]
    exact mul_neg_of_neg_of_pos hξneg hmpos
  linarith
