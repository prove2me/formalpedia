-- Prove2me | solution 1 for AvramDividend.Classical.left_affine_majorant_of_deriv_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:37:49.434423+00:00
-- url     : https://prove2.me/submissions/5d66bb54-5838-4a00-9eb2-563e8a35e3a2

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution (v : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hcont : ContinuousOn v (Icc 0 a))
    (hdiff : ∀ z ∈ Ioo 0 a, DifferentiableAt ℝ v z)
    (hder : ∀ z ∈ Ioo 0 a, 1 ≤ deriv v z) :
    ∀ z : ℝ, 0 ≤ z → z ≤ a → v z ≤ z - a + v a := by
  have hdOn : DifferentiableOn ℝ v (interior (Icc 0 a)) := by
    rw [interior_Icc]
    intro t ht
    exact (hdiff t ht).differentiableWithinAt
  have hderOn : ∀ t ∈ interior (Icc (0 : ℝ) a),
      (1 : ℝ) ≤ deriv v t := by
    intro t ht
    have hti : t ∈ Ioo (0 : ℝ) a := by
      simpa only [interior_Icc] using ht
    exact hder t hti
  intro z hz0 hza
  have hz : z ∈ Icc (0 : ℝ) a := ⟨hz0, hza⟩
  have haa : a ∈ Icc (0 : ℝ) a := ⟨ha, le_rfl⟩
  have hcore : (1 : ℝ) * (a - z) ≤ v a - v z :=
    (convex_Icc (0 : ℝ) a).mul_sub_le_image_sub_of_le_deriv
      hcont hdOn hderOn z hz a haa hza
  linarith
