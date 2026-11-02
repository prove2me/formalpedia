-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_C1_derivative_moving_base_uniform_finite_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:53:58.384718+00:00
-- url     : https://prove2.me/submissions/dde6798e-b14d-4596-8de6-166b4826938b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Set Filter

/-! Continuous C1 derivatives are uniformly stable under small translations
of the base point on each fixed compact negative-jump magnitude band. -/
theorem solution (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (x M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ b r : ℝ, |b - x| < δ → r ∈ Icc (0 : ℝ) M →
        |deriv w (b - r) - deriv w (x - r)| < ε := by
  have hCont : Continuous (deriv w) :=
    hwC1.continuous_deriv (by norm_num)
  have hUC : UniformContinuousOn (deriv w)
      (Icc (x - M - 1) (x + 1)) :=
    IsCompact.uniformContinuousOn_of_continuous isCompact_Icc hCont.continuousOn
  obtain ⟨η, hη, hmod⟩ :=
    Metric.uniformContinuousOn_iff.mp hUC ε hε
  refine ⟨min η 1, lt_min hη (by norm_num), ?_⟩
  intro b r hb hr
  have hb1 : |b - x| < 1 :=
    lt_of_lt_of_le hb (min_le_right _ _)
  have hbη : |b - x| < η :=
    lt_of_lt_of_le hb (min_le_left _ _)
  have hclose : x - 1 < b ∧ b < x + 1 := by
    rw [abs_lt] at hb1
    constructor <;> linarith [hb1.1, hb1.2]
  have hbase : x - r ∈ Icc (x - M - 1) (x + 1) := by
    constructor <;> linarith [hr.1, hr.2]
  have hmove : b - r ∈ Icc (x - M - 1) (x + 1) := by
    constructor <;> linarith [hclose.1, hclose.2, hr.1, hr.2]
  have hdist : dist (b - r) (x - r) < η := by
    calc
      dist (b - r) (x - r) = |b - x| := by
        rw [Real.dist_eq]
        congr 1
        ring
      _ < η := hbη
  have hh := hmod (b - r) hmove (x - r) hbase hdist
  simpa only [Real.dist_eq] using hh
