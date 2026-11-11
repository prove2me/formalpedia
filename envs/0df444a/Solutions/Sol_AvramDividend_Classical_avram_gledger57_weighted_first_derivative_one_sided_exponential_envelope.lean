-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger57_weighted_first_derivative_one_sided_exponential_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:17:54.337644+00:00
-- url     : https://prove2.me/submissions/93b62290-738c-4615-9571-cd3451e6ab78

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gsource15_exponential_derivative_comparison
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
noncomputable section

/-- A weighted first-derivative upper bound supplies a one-sided exponential
    majorant; the negative tail of the function remains unconstrained. -/
theorem solution
    (r l u : ℝ) (hr : l < r) (hu : 0 < u) (w : ℝ → ℝ)
    (hw : ∀ y : ℝ, u ≤ y → HasDerivAt w (deriv w y) y)
    (hweighted : ∀ y : ℝ, u ≤ y →
      Real.exp (-(r * y)) * (deriv w y - l * w y) ≤
        Real.exp (-(r * u)) * (deriv w u - l * w u)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, u ≤ y →
      w y ≤ K * Real.exp (r * y) := by
  let B : ℝ := Real.exp (-(r * u)) * (deriv w u - l * w u)
  let K : ℝ := max (w u * Real.exp (-(r * u))) (max (B / (r - l)) 0)
  have hrl : 0 < r - l := sub_pos.mpr hr
  have hK0 : 0 ≤ K := le_trans (le_max_right _ _) (le_max_right _ _)
  have hKwu : w u * Real.exp (-(r * u)) ≤ K := le_max_left _ _
  have hKB : B / (r - l) ≤ K :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hB : B ≤ K * (r - l) := (div_le_iff₀ hrl).mp hKB
  have hunit (z : ℝ) :
      Real.exp (-(r * z)) * Real.exp (r * z) = 1 := by
    rw [← Real.exp_add]
    have hzero : -(r * z) + r * z = 0 := by ring
    simp [hzero]
  have hKu : w u ≤ K * Real.exp (r * u) := by
    have h := mul_le_mul_of_nonneg_right hKwu (Real.exp_pos (r * u)).le
    calc
      w u = (w u * Real.exp (-(r * u))) * Real.exp (r * u) := by
        rw [mul_assoc, hunit u, mul_one]
      _ ≤ K * Real.exp (r * u) := h
  have hbound (t : ℝ) (ht : u ≤ t) :
      deriv w t - l * w t ≤ K * (r - l) * Real.exp (r * t) := by
    calc
      deriv w t - l * w t =
          (Real.exp (-(r * t)) * (deriv w t - l * w t)) *
            Real.exp (r * t) := by
        calc
          deriv w t - l * w t =
              (Real.exp (-(r * t)) * Real.exp (r * t)) *
                (deriv w t - l * w t) := by rw [hunit t]; ring
          _ = (Real.exp (-(r * t)) * (deriv w t - l * w t)) *
                Real.exp (r * t) := by ring
      _ ≤ B * Real.exp (r * t) :=
        mul_le_mul_of_nonneg_right (hweighted t ht) (Real.exp_pos _).le
      _ ≤ K * (r - l) * Real.exp (r * t) :=
        mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le
  let f : ℝ → ℝ := fun z => w z - K * Real.exp (r * z)
  have hfder (t : ℝ) (ht : u ≤ t) :
      HasDerivAt f (deriv w t - K * (r * Real.exp (r * t))) t := by
    have hlinear : HasDerivAt (fun z : ℝ => r * z) r t := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul r
    have hexp : HasDerivAt (fun z : ℝ => Real.exp (r * z))
        (r * Real.exp (r * t)) t := by
      simpa only [mul_comm] using hlinear.exp
    exact (hw t ht).sub (hexp.const_mul K)
  have hfineq (t : ℝ) (ht : u ≤ t) : deriv f t ≤ l * f t := by
    rw [(hfder t ht).deriv]
    dsimp [f]
    nlinarith [hbound t ht]
  refine ⟨K, hK0, ?_⟩
  intro y hy
  have hcomp : f y ≤ Real.exp (l * (y - u)) * f u :=
    avram_gsource15_exponential_derivative_comparison f u y l hy
      (by
        intro t ht
        rw [(hfder t ht.1).deriv]
        exact hfder t ht.1)
      (by intro t ht; exact hfineq t ht.1)
  have hfu : f u ≤ 0 := by dsimp [f]; linarith
  have hfy : f y ≤ 0 :=
    le_trans hcomp (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hfu)
  dsimp [f] at hfy
  linarith
