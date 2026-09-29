-- Prove2me | solution 1 for EthierKurtz.hessian_posSemidef_of_isLocalMin_on
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-27T21:20:02.187602+00:00
-- url     : https://prove2.me/submissions/727b8520-4825-42f7-8bfd-9f023c748214

import Mathlib

open scoped Topology

private theorem deriv2_nonneg_of_isLocalMin_on_aux
    {g : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hdiff : DifferentiableOn ℝ g (Metric.ball 0 r))
    (hg2 : DifferentiableAt ℝ (deriv g) 0)
    (hmin : IsLocalMin g 0) :
    0 ≤ deriv (deriv g) 0 := by
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
  set m := min (min (min ε₁ ε₂) (min r 1)) r / 2 with hmdef
  have hbase : 0 < min (min (min ε₁ ε₂) (min r 1)) r :=
    lt_min (lt_min (lt_min hε₁ hε₂) (lt_min hr one_pos)) hr
  have hmpos : 0 < m := by rw [hmdef]; linarith
  have hmlt : m < min (min (min ε₁ ε₂) (min r 1)) r := by
    rw [hmdef]; linarith
  have hm1 : m < ε₁ :=
    lt_of_lt_of_le hmlt
      (le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_left _ _))
  have hmr : m < r :=
    lt_of_lt_of_le hmlt (min_le_right _ _)
  have hm2 : m < ε₂ :=
    lt_of_lt_of_le hmlt
      (le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_right _ _))
  have hmball : m ∈ Metric.ball 0 r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hmpos]
    exact hmr
  have hmball2 : m ∈ Metric.ball 0 ε₂ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hmpos]
    exact hm2
  have hmmin : g 0 ≤ g m := hsub2 hmball2
  have hcont : ContinuousOn g (Set.Icc 0 m) := by
    refine DifferentiableOn.continuousOn (hdiff.mono ?_)
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
    hdiff.mono (fun x hx => by
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

theorem solution {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {x₀ : EuclideanSpace ℝ (Fin d)}
    {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : ContDiffOn ℝ 2 f s) (hmem : s ∈ 𝓝 x₀)
    (hmin : IsLocalMin f x₀) (v : EuclideanSpace ℝ (Fin d)) :
    0 ≤ (fderiv ℝ (fun y => fderiv ℝ f y v) x₀) v := by
  by_cases hv : v = 0
  · subst hv
    simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  obtain ⟨r₀, hr₀, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  set B := Metric.ball x₀ r₀ with hBdef
  have hsB : ContDiffOn ℝ 2 f B := hs.mono hsub
  have hBnbhd : B ∈ 𝓝 x₀ := Metric.ball_mem_nhds x₀ hr₀
  have hφ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x₀ + t • v) v t := fun t => by
    have h1 : HasDerivAt (fun x : ℝ => x • v) ((1:ℝ) • v) t :=
      (hasDerivAt_id t).smul_const v
    rw [one_smul] at h1
    have h2 := (hasDerivAt_const t x₀).add h1
    rw [zero_add] at h2
    exact h2
  have hφD : Differentiable ℝ (fun t : ℝ => x₀ + t • v) :=
    fun t => (hφ t).differentiableAt
  -- Directional-derivative map is differentiable at x₀ via ContDiffOn on the ball.
  have hU : UniqueDiffOn ℝ B :=
    uniqueDiffOn_convex (convex_ball x₀ r₀) (by
      have hInt : interior B = B := Metric.isOpen_ball.interior_eq
      rw [hInt]
      exact ⟨x₀, by rw [Metric.mem_ball, dist_self]; exact hr₀⟩)
  have hsB11 : ContDiffOn ℝ (1 + 1) f B := hsB
  have hHWithin : ContDiffOn ℝ 1
      (fun x => fderivWithin ℝ f B x v) B :=
    ((contDiffOn_succ_iff_fderiv_apply hU).mp hsB11).2.2 v
  have hHdiff : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x₀ := by
    have hW : DifferentiableOn ℝ (fun x => fderivWithin ℝ f B x v) B :=
      ContDiffOn.differentiableOn hHWithin one_ne_zero
    have hWx₀ : DifferentiableAt ℝ (fun x => fderivWithin ℝ f B x v) x₀ :=
      hW.differentiableAt hBnbhd
    have heq : (fun y => fderiv ℝ f y v) =ᶠ[𝓝 x₀]
        (fun x => fderivWithin ℝ f B x v) :=
      Filter.eventuallyEq_of_mem hBnbhd (fun x hx => by
        have hxnbhd : B ∈ 𝓝 x := Metric.isOpen_ball.mem_nhds hx
        rw [fderivWithin_of_mem_nhds hxnbhd])
    exact hWx₀.congr_of_eventuallyEq heq
  -- The line stays in the ball on a small interval.
  set R := r₀ / (‖v‖ + 1) with hRdef
  have hR : 0 < R := div_pos hr₀ (by positivity)
  have hRv : R * ‖v‖ < r₀ := by
    have h1 : (0:ℝ) < ‖v‖ + 1 := by positivity
    rw [hRdef, div_mul_eq_mul_div, div_lt_iff₀ h1]
    nlinarith [hr₀]
  have hmaps : Set.MapsTo (fun t : ℝ => x₀ + t • v) (Metric.ball 0 R) B := by
    intro t ht
    have htR : |t| < R := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      exact ht
    have htv : ‖t • v‖ < r₀ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right (le_of_lt htR) (norm_nonneg _))
        hRv
    have hdist : dist (x₀ + t • v) x₀ < r₀ := by
      rw [dist_eq_norm, add_sub_cancel_left]
      exact htv
    show x₀ + t • v ∈ B
    rw [hBdef, Metric.mem_ball]
    exact hdist
  have hdiffGOn : DifferentiableOn ℝ (fun t : ℝ => f (x₀ + t • v))
      (Metric.ball 0 R) := by
    have hdiffOnB : DifferentiableOn ℝ f B :=
      ContDiffOn.differentiableOn hsB (by simp)
    exact hdiffOnB.comp hφD.differentiableOn hmaps
  have eφ0 : (fun t : ℝ => x₀ + t • v) (0:ℝ) = x₀ := by simp
  have e1 : ∀ t ∈ Metric.ball (0:ℝ) R, deriv (fun t : ℝ => f (x₀ + t • v)) t
      = (fderiv ℝ f ((fun t : ℝ => x₀ + t • v) t)) v := by
    intro t ht
    have hBt : (fun t : ℝ => x₀ + t • v) t ∈ B := hmaps ht
    have hF : HasFDerivAt f (fderiv ℝ f ((fun t : ℝ => x₀ + t • v) t))
        ((fun t : ℝ => x₀ + t • v) t) := by
      have hdiffOnB : DifferentiableOn ℝ f B :=
        ContDiffOn.differentiableOn hsB (by simp)
      have hAt : DifferentiableAt ℝ f ((fun t : ℝ => x₀ + t • v) t) :=
        hdiffOnB.differentiableAt (Metric.isOpen_ball.mem_nhds hBt)
      exact hAt.hasFDerivAt
    have hc := (hF.comp_hasDerivAt t (hφ t)).deriv
    simpa only [Function.comp_def] using hc
  have hgg : Set.EqOn (deriv (fun t : ℝ => f (x₀ + t • v)))
      ((fun y => fderiv ℝ f y v) ∘ (fun t : ℝ => x₀ + t • v))
      (Metric.ball 0 R) :=
    fun t ht => e1 t ht
  have hHder : HasDerivAt
      ((fun y => fderiv ℝ f y v) ∘ (fun t : ℝ => x₀ + t • v))
      ((fderiv ℝ (fun y => fderiv ℝ f y v) x₀) v) (0:ℝ) := by
    have hH'at : HasFDerivAt (fun y => fderiv ℝ f y v)
        (fderiv ℝ (fun y => fderiv ℝ f y v) x₀)
        ((fun t : ℝ => x₀ + t • v) (0:ℝ)) := by
      rw [eφ0]
      exact hHdiff.hasFDerivAt
    exact hH'at.comp_hasDerivAt (0:ℝ) (hφ (0:ℝ))
  have hEq : deriv (fun t : ℝ => f (x₀ + t • v)) =ᶠ[𝓝 (0:ℝ)]
      ((fun y => fderiv ℝ f y v) ∘ (fun t : ℝ => x₀ + t • v)) :=
    Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds 0 hR) hgg
  have hcontφ : ContinuousAt (fun t : ℝ => x₀ + t • v) (0:ℝ) :=
    (hφ (0:ℝ)).continuousAt
  have hminφ : IsLocalMin f ((fun t : ℝ => x₀ + t • v) (0:ℝ)) := by
    rw [eφ0]
    exact hmin
  have hming : IsLocalMin (fun t : ℝ => f (x₀ + t • v)) (0:ℝ) :=
    hcontφ hminφ
  have hg2g : DifferentiableAt ℝ (deriv (fun t : ℝ => f (x₀ + t • v))) (0:ℝ) :=
    hHder.differentiableAt.congr_of_eventuallyEq hEq
  have h1d := deriv2_nonneg_of_isLocalMin_on_aux hR hdiffGOn hg2g hming
  have hident : deriv (deriv (fun t : ℝ => f (x₀ + t • v))) (0:ℝ)
      = (fderiv ℝ (fun y => fderiv ℝ f y v) x₀) v := by
    rw [hEq.deriv_eq]
    exact hHder.deriv
  exact hident ▸ h1d
