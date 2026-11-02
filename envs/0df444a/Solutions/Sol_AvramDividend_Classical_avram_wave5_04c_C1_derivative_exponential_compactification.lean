-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_C1_derivative_exponential_compactification
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:43:39.318496+00:00
-- url     : https://prove2.me/submissions/5b335426-54aa-45c9-a1dc-1ab6c3b33004

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Set Filter

/-! Construct a bounded continuous, zero-at-zero extension of the C1 derivative
under the exponential compactification r ↦ exp(-r). -/
theorem solution (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x M : ℝ) (hM : 0 ≤ M) :
    ∃ F : ℝ → ℝ, Continuous F ∧ F 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, |F t| ≤ L) ∧
      (∀ r ∈ Icc (0 : ℝ) M,
        F (Real.exp (-r)) = deriv w (x - r)) := by
  let δ : ℝ := Real.exp (-M)
  have hδ : 0 < δ := Real.exp_pos _
  let F : ℝ → ℝ := fun t =>
    min (1 : ℝ) (t / δ) * deriv w (x + Real.log (max t δ))
  have hlog : Continuous (fun t : ℝ => Real.log (max t δ)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hp : max t δ ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le hδ (le_max_right t δ))
    exact (continuous_id.max continuous_const).continuousAt.log hp
  have hcont : Continuous F := by
    exact (continuous_const.min (continuous_id.div_const δ)).mul
      ((hwC1.continuous_deriv (by norm_num)).comp
        (continuous_const.add hlog))
  have hzero : F 0 = 0 := by
    simp [F]
  have hLip' : LipschitzWith (Real.toNNReal L) w := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simpa [Real.dist_eq, Real.coe_toNNReal, hL] using hLip u v
  have hDerBound (y : ℝ) : |deriv w y| ≤ L := by
    simpa only [Real.norm_eq_abs, Real.coe_toNNReal, hL] using
      (norm_deriv_le_of_lipschitz (x₀ := y) hLip')
  have hBound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |F t| ≤ L := by
    have ht0 : 0 ≤ t := ht.1
    have hfac0 : 0 ≤ min (1 : ℝ) (t / δ) :=
      le_min (by norm_num) (div_nonneg ht0 hδ.le)
    have hfac1 : min (1 : ℝ) (t / δ) ≤ 1 := min_le_left _ _
    calc
      |F t| = min (1 : ℝ) (t / δ) *
          |deriv w (x + Real.log (max t δ))| := by
            simp [F, abs_mul, abs_of_nonneg hfac0]
      _ ≤ min (1 : ℝ) (t / δ) * L :=
        mul_le_mul_of_nonneg_left (hDerBound _) hfac0
      _ ≤ L := by simpa using mul_le_mul_of_nonneg_right hfac1 hL
  have hEq (r : ℝ) (hr : r ∈ Icc (0 : ℝ) M) :
      F (Real.exp (-r)) = deriv w (x - r) := by
    have he : δ ≤ Real.exp (-r) :=
      Real.exp_le_exp.mpr (by linarith [hr.2])
    have hfac : 1 ≤ Real.exp (-r) / δ := by
      apply (le_div_iff₀ hδ).mpr
      simpa using he
    simp [F, min_eq_left hfac, max_eq_left he, Real.log_exp, sub_eq_add_neg]
  exact ⟨F, hcont, hzero, hBound, hEq⟩
