-- Prove2me | solution 1 for BranchSpectral.kernel_summable
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:18:10.77528+00:00
-- url     : https://prove2.me/submissions/7ba70bcf-4835-400f-ad6a-f545be9dabc0

import Mathlib
open MeasureTheory Set Filter Topology


theorem BranchSpectral.atom_abs_bound_aux (g e t : ℝ) (he : |e| ≤ 1/2) (ht : 0 < t) :
    |(fun (g e t : ℝ) => Real.exp (-(g^2-e^2)*t)*Real.cos (2*e*g*t)) g e t| ≤ Real.exp (t/4)*(fun (g t : ℝ) => Real.exp (-g^2*t)) g t := by
  simp only
  rw [abs_mul, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  calc Real.exp (-(g ^ 2 - e ^ 2) * t) * |Real.cos (2 * e * g * t)|
      ≤ Real.exp (-(g ^ 2 - e ^ 2) * t) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
    _ ≤ Real.exp (t / 4 + -g ^ 2 * t) := by
        rw [mul_one]
        apply Real.exp_le_exp.2
        have : e ^ 2 ≤ 1 / 4 := by
          have h0 : 0 ≤ |e| := abs_nonneg e
          have : |e| ^ 2 ≤ (1/2) ^ 2 := pow_le_pow_left₀ h0 he 2
          rw [sq_abs] at this; linarith
        nlinarith

theorem BranchSpectral.kernel_summable (g e : ℕ → ℝ) (t : ℝ)
    (he : ∀ j, |e j| ≤ 1/2) (ht : 0 < t)
    (hg : Summable (fun j => (fun (g t : ℝ) => Real.exp (-g^2*t)) (g j) t)) :
    Summable (fun j => (fun (g e t : ℝ) => Real.exp (-(g^2-e^2)*t)*Real.cos (2*e*g*t)) (g j) (e j) t) := by
  refine Summable.of_norm_bounded (hg.mul_left (Real.exp (t/4))) (fun j => ?_)
  rw [Real.norm_eq_abs]
  exact BranchSpectral.atom_abs_bound_aux (g j) (e j) t (he j) ht

theorem solution (g e : ℕ → ℝ) (t : ℝ)
    (he : ∀ j, |e j| ≤ 1/2) (ht : 0 < t)
    (hg : Summable (fun j => (fun (g t : ℝ) => Real.exp (-g^2*t)) (g j) t)) :
    Summable (fun j => (fun (g e t : ℝ) => Real.exp (-(g^2-e^2)*t)*Real.cos (2*e*g*t)) (g j) (e j) t) := by
  refine Summable.of_norm_bounded (hg.mul_left (Real.exp (t/4))) (fun j => ?_)
  rw [Real.norm_eq_abs]
  exact BranchSpectral.atom_abs_bound_aux (g j) (e j) t (he j) ht
