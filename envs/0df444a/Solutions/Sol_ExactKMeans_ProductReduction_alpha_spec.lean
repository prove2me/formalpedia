-- Prove2me | solution 1 for ExactKMeans.ProductReduction.alpha_spec
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-15T18:49:00.018139+00:00
-- url     : https://prove2.me/submissions/0071f8ce-deb3-4053-947d-a82a61471bef

import Definitions.Def_ExactKMeans_ProductReduction_Selector

open scoped BigOperators Classical
open Finset
open ExactKMeans.ProductReduction

namespace KMeansAlpha

lemma lam_ge (p : Parameters) : (p.t : ℝ) + 1 ≤ p.lam := by
  have hN : 2 * p.t ≤ p.N := by
    unfold Parameters.N; exact Nat.mul_le_mul_right p.t p.q_ge
  have h12 : p.N ≤ p.N ^ 12 := Nat.le_self_pow (by norm_num) _
  have : p.t + 1 ≤ p.lam := by unfold Parameters.lam; omega
  exact_mod_cast this

lemma alpha_exists (p : Parameters) : ∃ x : ℝ, 0 < x ∧ (1 / 2 : ℝ) < x * p.lam ∧ x * p.lam < 1 ∧
    (p.lam : ℝ) * Real.sin x = Real.cos (((p.t : ℝ) - 1) * x) := by
  have hL := lam_ge p
  have ht : (3 : ℝ) ≤ p.t := by exact_mod_cast p.t_ge
  set L : ℝ := (p.lam : ℝ) with hLdef
  have hLpos : 0 < L := by linarith
  let f : ℝ → ℝ := fun x => L * Real.sin x - Real.cos (((p.t : ℝ) - 1) * x)
  have hcont : Continuous f := by fun_prop
  have hab : 1 / (2 * L) < 1 / L := by
    apply one_div_lt_one_div_of_lt hLpos; linarith
  have hfa : f (1 / (2 * L)) < 0 := by
    have hu : 0 < 1 / (2 * L) := by positivity
    have h1 : Real.sin (1 / (2 * L)) < 1 / (2 * L) := Real.sin_lt hu
    have h2 := Real.one_sub_sq_div_two_le_cos (x := ((p.t : ℝ) - 1) * (1 / (2 * L)))
    have hy : ((p.t : ℝ) - 1) * (1 / (2 * L)) < 1 := by
      rw [mul_one_div, div_lt_one (by positivity)]; linarith
    have hy0 : 0 < ((p.t : ℝ) - 1) * (1 / (2 * L)) := by
      apply mul_pos <;> [linarith; positivity]
    have h3 : L * Real.sin (1 / (2 * L)) < 1 / 2 := by
      calc L * Real.sin (1 / (2 * L)) < L * (1 / (2 * L)) := mul_lt_mul_of_pos_left h1 hLpos
        _ = 1 / 2 := by field_simp
    show L * Real.sin (1 / (2 * L)) - Real.cos (((p.t : ℝ) - 1) * (1 / (2 * L))) < 0
    nlinarith
  have hfb : 0 < f (1 / L) := by
    set u : ℝ := 1 / L with hu
    have hLu : L * u = 1 := by rw [hu]; field_simp
    have hu0 : 0 < u := by positivity
    have hu1 : u ≤ 1 := by rw [hu, div_le_one hLpos]; linarith
    have h1 := Real.sin_gt_sub_cube hu0
    set y : ℝ := ((p.t : ℝ) - 1) * u with hy
    have hy0 : 0 ≤ y := by rw [hy]; apply mul_nonneg <;> linarith
    have hy1 : y ≤ 1 := by
      rw [hy]
      calc ((p.t : ℝ) - 1) * u ≤ L * u := by
            apply mul_le_mul_of_nonneg_right <;> linarith
        _ = 1 := hLu
    have h2 := Real.cos_bound (x := y) (by rw [abs_of_nonneg hy0]; exact hy1)
    rw [abs_of_nonneg hy0] at h2
    have h2' : Real.cos y ≤ 1 - y ^ 2 / 2 + y ^ 4 * (5 / 96) := by
      have := (abs_le.mp h2).2; linarith
    have hy4 : y ^ 4 ≤ y ^ 2 := by
      have : y ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg y]
    have hyu : 4 * u ^ 2 ≤ y ^ 2 := by
      rw [hy]; have : (2:ℝ) ≤ (p.t : ℝ) - 1 := by linarith
      have h4 : (4:ℝ) ≤ ((p.t : ℝ) - 1) ^ 2 := by nlinarith
      rw [mul_pow]; nlinarith [sq_nonneg u]
    have h3 : L * Real.sin u > L * (u - u ^ 3 / 6) := mul_lt_mul_of_pos_left h1 hLpos
    have h4 : L * (u - u ^ 3 / 6) = 1 - u ^ 2 / 6 := by
      have : L * (u - u ^ 3 / 6) = L * u - (L * u) * u ^ 2 / 6 := by ring
      rw [this, hLu]; ring
    show 0 < L * Real.sin u - Real.cos y
    nlinarith
  obtain ⟨c, ⟨hc1, hc2⟩, hfc⟩ :=
    intermediate_value_Ioo hab.le hcont.continuousOn (show (0 : ℝ) ∈ Set.Ioo _ _ from ⟨hfa, hfb⟩)
  refine ⟨c, lt_trans (by positivity) hc1, ?_, ?_, ?_⟩
  · have := mul_lt_mul_of_pos_right hc1 hLpos
    rwa [show 1 / (2 * L) * L = 1 / 2 by field_simp] at this
  · have := mul_lt_mul_of_pos_right hc2 hLpos
    rwa [show 1 / L * L = 1 by field_simp] at this
  · have : L * Real.sin c - Real.cos (((p.t : ℝ) - 1) * c) = 0 := hfc
    linarith

lemma alpha_spec' (p : Parameters) : 0 < p.alpha ∧ (1 / 2 : ℝ) < p.alpha * p.lam ∧
    p.alpha * p.lam < 1 ∧ (p.lam : ℝ) * Real.sin p.alpha = Real.cos (((p.t : ℝ) - 1) * p.alpha) := by
  unfold Parameters.alpha
  exact Classical.epsilon_spec (alpha_exists p)


end KMeansAlpha

open KMeansAlpha in
theorem solution (p : Parameters) :
    0 < p.alpha ∧ (1 / 2 : ℝ) < p.alpha * p.lam ∧ p.alpha * p.lam < 1 ∧
      (p.lam : ℝ) * Real.sin p.alpha = Real.cos (((p.t : ℝ) - 1) * p.alpha) ∧
      0 < Real.sin p.alpha ∧ 0 < p.r := by
  obtain ⟨hα0, h1, hα1, h2⟩ := alpha_spec' p
  have hL := lam_ge p
  have ht : (3 : ℝ) ≤ p.t := by exact_mod_cast p.t_ge
  have hα : p.alpha < 1 := by nlinarith
  have hs : 0 < Real.sin p.alpha :=
    Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_gt_three])
  have hb : (0 : ℝ) < p.b := by exact_mod_cast p.b_pos
  have hN : (0 : ℝ) < p.N := by
    unfold Parameters.N; have := p.a_pos; have := p.b_pos; have := p.t_ge; positivity
  refine ⟨hα0, h1, hα1, h2, hs, ?_⟩
  unfold Parameters.r; positivity
