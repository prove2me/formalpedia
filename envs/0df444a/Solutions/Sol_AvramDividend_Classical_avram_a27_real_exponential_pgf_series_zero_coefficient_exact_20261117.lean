-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_real_exponential_pgf_series_zero_coefficient_exact_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T19:03:05.833346+00:00
-- url     : https://prove2.me/submissions/3f39aea3-9c6c-492a-ab87-4d970cc37c90

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
noncomputable section

/-- The constant coefficient of a marked exponential PGF is the zero-argument exponential. -/
theorem solution (C : ℕ → ℝ) (r q : ℝ)
    (hSeries : ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      HasSum (fun k : ℕ => z ^ k * C k) (Real.exp (q * z - r))) :
    C 0 = Real.exp (-r) := by
  have h0 := hSeries 0 (le_refl 0) (by norm_num)
  have hId : (fun k : ℕ => (0 : ℝ) ^ k * C k) =
      (fun k : ℕ => if k = 0 then C 0 else 0) := by
    funext k
    by_cases hk : k = 0
    · subst k
      simp
    · simp [hk]
  rw [hId] at h0
  have hSingle : HasSum (fun k : ℕ => if k = 0 then C 0 else 0)
      (C 0) := hasSum_ite_eq 0 (C 0)
  have hSum : C 0 = Real.exp (q * 0 - r) :=
    hSingle.unique h0
  simpa using hSum
