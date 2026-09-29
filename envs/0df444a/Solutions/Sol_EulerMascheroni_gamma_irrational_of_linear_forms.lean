-- Prove2me | solution 1 for EulerMascheroni.gamma_irrational_of_linear_forms
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-10T07:03:21.818613+00:00
-- url     : https://prove2.me/submissions/6167e4c8-f6d0-4315-a77a-a253b726362f

import Mathlib

open Real Filter Topology

theorem solution
    (p q : ℕ → ℤ)
    (hne : ∀ n, (q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ) ≠ 0)
    (hlim : Filter.Tendsto (fun n => (q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ))
      Filter.atTop (nhds 0)) :
    Irrational Real.eulerMascheroniConstant := by
  rintro ⟨r, hr⟩
  have hden : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.pos
  have hrr : Real.eulerMascheroniConstant = (r.num : ℝ) / (r.den : ℝ) := by
    rw [← hr]; exact_mod_cast (Rat.num_div_den r).symm
  -- every linear form is an integer divided by the fixed denominator `r.den`
  have hLN : ∀ n, (q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ)
      = ((q n * r.num - p n * (r.den : ℤ) : ℤ) : ℝ) / (r.den : ℝ) := by
    intro n
    rw [hrr]
    push_cast
    field_simp
  -- a non-zero integer has absolute value at least one, so the forms cannot get small
  have hkey : ∀ n, 1 / (r.den : ℝ)
      ≤ |(q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ)| := by
    intro n
    have h0 : q n * r.num - p n * (r.den : ℤ) ≠ 0 := by
      intro h
      exact hne n (by rw [hLN n, h]; simp)
    have h1 : (1 : ℝ) ≤ |((q n * r.num - p n * (r.den : ℤ) : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs h0
    rw [hLN n, abs_div, abs_of_pos hden]
    gcongr
  -- but they tend to zero
  have habs : Filter.Tendsto
      (fun n => |(q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ)|)
      Filter.atTop (nhds 0) := by simpa using hlim.abs
  obtain ⟨n, hn⟩ := (habs.eventually (gt_mem_nhds (show (0:ℝ) < 1 / (r.den : ℝ) by positivity))).exists
  exact absurd hn (not_lt.mpr (hkey n))
