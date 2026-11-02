-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_uniform_interior_cutoffs_with_favourable_kinks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:46:20.582746+00:00
-- url     : https://prove2.me/submissions/37ca2bd9-7e6d-40ea-adc9-bd64b200a9d8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_cap_corner_countable_uniform_cutoff_sequence_with_cap_proximity
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_interior_cap_cutoff_one_sided_derivatives_favourable_kink

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology Filter AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-!
Every member of a single global uniformly accurate interior
cap-localisation sequence has a finite nonpositive Tanaka kink.
The true cap requires no derivative or C² hypothesis.
-/

theorem solution
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y) :
    ∃ b : ℕ → ℝ,
      (∀ n : ℕ, 0 < b n ∧ b n < c ∧
        c - b n < 1 / ((n : ℝ) + 1)) ∧
      (∀ (n : ℕ),
        HasDerivWithinAt
          (fun y : ℝ => if y ≤ b n then w y else w (b n) + (y - b n))
          (deriv w (b n)) (Iic (b n)) (b n) ∧
        HasDerivWithinAt
          (fun y : ℝ => if y ≤ b n then w y else w (b n) + (y - b n))
          1 (Ici (b n)) (b n) ∧
        1 - deriv w (b n) ≤ 0) ∧
      ∀ (n : ℕ) (y : ℝ), 0 ≤ y →
        0 ≤ (if y ≤ c then w y else w c + (y - c)) -
          (if y ≤ b n then w y else w (b n) + (y - b n)) ∧
        (if y ≤ c then w y else w c + (y - c)) -
          (if y ≤ b n then w y else w (b n) + (y - b n)) <
          1 / ((n : ℝ) + 1) := by
  obtain ⟨b, hLoc, hUniform⟩ :=
    avram_wave5_05_ubv_cap_corner_countable_uniform_cutoff_sequence_with_cap_proximity
      w c hc hw_cont hw_smooth hw_grad
  refine ⟨b, hLoc, ?_, hUniform⟩
  have hInterior :
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c} =
        Ioo (0 : ℝ) c := by
    ext y
    simp only [mem_setOf_eq, mem_Ioo]
    constructor
    · rintro ⟨hy0, hyC⟩
      exact ⟨hy0, (ENNReal.ofReal_lt_ofReal_iff hc).mp hyC⟩
    · rintro ⟨hy0, hyC⟩
      exact ⟨hy0, (ENNReal.ofReal_lt_ofReal_iff hc).mpr hyC⟩
  rw [hInterior] at hw_smooth
  have hDiffOn : DifferentiableOn ℝ w (Ioo (0 : ℝ) c) :=
    hw_smooth.differentiableOn (by norm_num)
  intro n
  have hn : b n ∈ Ioo (0 : ℝ) c :=
    ⟨(hLoc n).1, (hLoc n).2.1⟩
  have hDiff : DifferentiableAt ℝ w (b n) :=
    (hDiffOn (b n) hn).differentiableAt (isOpen_Ioo.mem_nhds hn)
  have hSlope : 1 ≤ deriv w (b n) :=
    hw_grad (b n) (hLoc n).1
      ((ENNReal.ofReal_lt_ofReal_iff hc).mpr (hLoc n).2.1)
  exact
    avram_wave5_05_interior_cap_cutoff_one_sided_derivatives_favourable_kink
      w (b n) hDiff hSlope
