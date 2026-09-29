-- Prove2me | solution 1 for BiconvexProg.Boundary.bilinear_local_solutions
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:00:34.97412+00:00
-- url     : https://prove2.me/submissions/af4b26a3-3c8e-4a4a-a070-84c94933f391

import Mathlib

theorem solution :
    let B : Set (ℝ × ℝ) := {z | -1 ≤ z.1 ∧ z.1 ≤ 2 ∧ -2 ≤ z.2 ∧ z.2 ≤ 3}
    let f : ℝ × ℝ → ℝ := fun z => z.1 * z.2
    IsLocalMinOn f B ((-1 : ℝ), (3 : ℝ)) ∧ IsLocalMinOn f B ((2 : ℝ), (-2 : ℝ)) ∧
      ¬ IsMinOn f B ((-1 : ℝ), (3 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · have hopen : IsOpen {z : ℝ × ℝ | 0 < z.2} := isOpen_lt continuous_const continuous_snd
    have hmem : ((-1 : ℝ), (3 : ℝ)) ∈ {z : ℝ × ℝ | 0 < z.2} := by
      show (0 : ℝ) < 3
      norm_num
    filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hmem), self_mem_nhdsWithin]
      with z hz hzB
    obtain ⟨hz1, hz2, hz3, hz4⟩ := hzB
    have hzpos : (0 : ℝ) < z.2 := hz
    show (-1 : ℝ) * 3 ≤ z.1 * z.2
    nlinarith
  · have hopen : IsOpen {z : ℝ × ℝ | 0 < z.1} := isOpen_lt continuous_const continuous_fst
    have hmem : ((2 : ℝ), (-2 : ℝ)) ∈ {z : ℝ × ℝ | 0 < z.1} := by
      show (0 : ℝ) < 2
      norm_num
    filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hmem), self_mem_nhdsWithin]
      with z hz hzB
    obtain ⟨hz1, hz2, hz3, hz4⟩ := hzB
    have hzpos : (0 : ℝ) < z.1 := hz
    show (2 : ℝ) * (-2) ≤ z.1 * z.2
    nlinarith
  · intro hmin
    have hmem : ((2 : ℝ), (-2 : ℝ)) ∈
        {z : ℝ × ℝ | -1 ≤ z.1 ∧ z.1 ≤ 2 ∧ -2 ≤ z.2 ∧ z.2 ≤ 3} := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num
    have h := isMinOn_iff.mp hmin _ hmem
    have h' : (-1 : ℝ) * 3 ≤ (2 : ℝ) * (-2) := h
    norm_num at h'
