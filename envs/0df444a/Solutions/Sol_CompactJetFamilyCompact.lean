-- Prove2me | solution 1 for CompactJetFamilyCompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:21:54.033718+00:00
-- url     : https://prove2.me/submissions/7c1fc9d3-86e3-4690-bc8b-4b49956b9bfa

import Definitions.Def_PHigherOrder_CompactJetFamily
import Definitions.Def_PHigherOrder_PHarmJetEquicontinuity
import Definitions.Def_PHigherOrder_CompactJetFamilyCompact
import Theorems.Thm_PHarmJetEquicontinuity


set_option autoImplicit false

theorem _root_.solution (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (F : FirstOrderEstimateInput p) :
    IsCompact (CompactJetFamily p) := by
  -- Step 0: the two ball inclusions `XHalf ⊆ B_{3/4} ⊆ B_1`.
  have hhalf : ∀ x : XHalf, ‖(x : Plane)‖ ≤ 1 / 2 := by
    intro x
    have hx := x.2
    rwa [Metric.mem_closedBall, dist_zero_right] at hx
  have hin34 : ∀ x : XHalf, (x : Plane) ∈ Metric.ball (0 : Plane) (3 / 4) := by
    intro x
    rw [Metric.mem_ball, dist_zero_right]
    linarith [hhalf x]
  have hin1 : ∀ x : XHalf, (x : Plane) ∈ Metric.ball (0 : Plane) 1 := by
    intro x
    rw [Metric.mem_ball, dist_zero_right]
    linarith [hhalf x]
  -- `‖gradient v y‖` and `‖fderiv ℝ v y‖` agree, the Riesz map being an isometry; the mean
  -- value inequality is stated for `fderiv`, the estimate for `gradient`.
  have hfd : ∀ (v : Plane → ℝ) (y : Plane), ‖fderiv ℝ v y‖ = ‖gradient v y‖ := by
    intro v y
    rw [← toDual_gradient]
    exact (InnerProductSpace.toDual ℝ Plane).norm_map _
  -- Step 1: the estimates on a generator, transported to `x₀ = 0`, `R = 1/2`, `M = 1`, where
  -- `2 * R = 1`, `3 * R / 2 = 3/4` and `F.C₀ * M / (2 * R) = F.C₀`.
  have hR : (2 : ℝ) * (1 / 2) = 1 := by norm_num
  have hR32 : (3 : ℝ) * (1 / 2) / 2 = 3 / 4 := by norm_num
  have hest : ∀ (v : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) v g →
      (∀ y ∈ Metric.ball (0 : Plane) 1, |v y| ≤ 1) →
      (∀ y ∈ Metric.ball (0 : Plane) (3 / 4), DifferentiableAt ℝ v y) ∧
      (∀ y ∈ Metric.ball (0 : Plane) (3 / 4), ‖gradient v y‖ ≤ F.C₀) ∧
      (∀ y ∈ Metric.ball (0 : Plane) (3 / 4), ∀ y' ∈ Metric.ball (0 : Plane) (3 / 4),
        ‖gradient v y - gradient v y'‖ ≤ F.C₀ * ‖y - y'‖ ^ F.kappa) := by
    intro v g hv hbd
    have h := PHarmJetEquicontinuity p hp hp2 F 0 (1 / 2) 1 (by norm_num) (by norm_num) v g
      (by rw [hR]; exact hv) (by rw [hR]; exact hbd)
    rw [hR32, hR] at h
    simp only [mul_one, div_one] at h
    refine ⟨fun y hy => ?_, h.2.1, h.2.2⟩
    exact (h.1.differentiableOn one_ne_zero).differentiableAt (Metric.isOpen_ball.mem_nhds hy)
  -- Step 4: Arzela-Ascoli in its bundled form, on the compact base `XHalf`.
  rw [CompactJetFamily]
  refine BoundedContinuousFunction.arzela_ascoli
    (Set.Icc (-1 : ℝ) 1 ×ˢ Metric.closedBall (0 : Plane) F.C₀)
    (isCompact_Icc.prod (isCompact_closedBall _ _)) _ ?_ ?_
  · -- Step 2: every jet value lies in that fixed compact set.
    intro f x hf
    obtain ⟨v, g, hv, hbd, _, hz⟩ := hf
    obtain ⟨_, hgrad, _⟩ := hest v g hv hbd
    rw [hz x]
    refine Set.mem_prod.mpr ⟨Set.mem_Icc.mpr (abs_le.mp (hbd (x : Plane) (hin1 x))), ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hgrad (x : Plane) (hin34 x)
  · -- Step 3: equicontinuity through a single global modulus, uniform over the family.
    refine Metric.equicontinuous_of_continuity_modulus
      (fun t : ℝ => F.C₀ * t + F.C₀ * t ^ F.kappa) ?_ _ ?_
    · -- The modulus tends to `0` at `0`:  `t ↦ t ^ F.kappa` is continuous there because
      -- `F.kappa > 0`, and its value at `0` is `0`.
      have hcont : ContinuousAt (fun t : ℝ => F.C₀ * t + F.C₀ * t ^ F.kappa) 0 :=
        ((continuous_const.mul continuous_id).continuousAt).add
          (continuousAt_const.mul
            (Real.continuousAt_rpow_const 0 F.kappa (Or.inr F.kappa_pos.le)))
      have htend : Filter.Tendsto (fun t : ℝ => F.C₀ * t + F.C₀ * t ^ F.kappa) (nhds 0)
          (nhds (F.C₀ * 0 + F.C₀ * (0 : ℝ) ^ F.kappa)) := hcont
      have h0 : F.C₀ * 0 + F.C₀ * (0 : ℝ) ^ F.kappa = 0 := by
        rw [Real.zero_rpow (ne_of_gt F.kappa_pos)]; ring
      rwa [h0] at htend
    · intro x y i
      obtain ⟨v, g, hv, hbd, _, hz⟩ := i.2
      obtain ⟨hdiff, hgrad, hhol⟩ := hest v g hv hbd
      have hd : dist x y = ‖(x : Plane) - (y : Plane)‖ := by
        rw [Subtype.dist_eq, dist_eq_norm]
      -- First components: the mean value inequality on the convex ball `B_{3/4}`.
      have h1 : ‖v (x : Plane) - v (y : Plane)‖ ≤ F.C₀ * ‖(x : Plane) - (y : Plane)‖ :=
        Convex.norm_image_sub_le_of_norm_fderiv_le hdiff
          (fun z hz => by rw [hfd v z]; exact hgrad z hz)
          (convex_ball _ _) (hin34 y) (hin34 x)
      -- Second components: the `F.kappa`-Holder bound, directly.
      have h2 : ‖gradient v (x : Plane) - gradient v (y : Plane)‖
          ≤ F.C₀ * ‖(x : Plane) - (y : Plane)‖ ^ F.kappa :=
        hhol _ (hin34 x) _ (hin34 y)
      show dist ((i.1 : BoundedContinuousFunction XHalf (ℝ × Plane)) x)
        ((i.1 : BoundedContinuousFunction XHalf (ℝ × Plane)) y)
          ≤ F.C₀ * dist x y + F.C₀ * dist x y ^ F.kappa
      rw [hz x, hz y]
      simp only [Prod.dist_eq, hd]
      refine max_le ?_ ?_
      · rw [Real.dist_eq]
        refine le_trans ?_ (le_add_of_nonneg_right
          (mul_nonneg F.C₀_pos.le (Real.rpow_nonneg (norm_nonneg _) _)))
        rw [← Real.norm_eq_abs]
        exact h1
      · rw [dist_eq_norm]
        exact le_trans h2 (le_add_of_nonneg_left (mul_nonneg F.C₀_pos.le (norm_nonneg _)))
