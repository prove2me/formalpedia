-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_canonical_negative_mark_bands_antitone_empty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:08:18.558836+00:00
-- url     : https://prove2.me/submissions/19086be3-7ccd-4e7f-926b-12a0aa3ba639

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section

/-- The physically relevant small-negative jump bands (-1/(n+1),0)
decrease to the empty set, allowing exact L2 tail estimates. -/
theorem solution :
    Antitone (fun n : ℕ =>
      Ioo (-(1 : ℝ) / ((n + 1 : ℕ) : ℝ)) (0 : ℝ)) ∧
    (⋂ n : ℕ, Ioo (-(1 : ℝ) / ((n + 1 : ℕ) : ℝ)) (0 : ℝ)) = ∅ := by
  constructor
  · intro n m hnm z hz
    have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hle : ((n + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hnm 1
    have hinv : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ≤
        (1 : ℝ) / ((n + 1 : ℕ) : ℝ) :=
      one_div_le_one_div_of_le hpos hle
    have hzlow : -((1 : ℝ) / ((m + 1 : ℕ) : ℝ)) < z := by
      simpa only [neg_div] using hz.1
    have hnlow : -((1 : ℝ) / ((n + 1 : ℕ) : ℝ)) < z := by
      linarith [hzlow, hinv]
    exact ⟨by simpa only [neg_div] using hnlow, hz.2⟩
  · apply Set.ext
    intro z
    constructor
    · intro hz
      have hAll : ∀ n : ℕ,
          z ∈ Ioo (-(1 : ℝ) / ((n + 1 : ℕ) : ℝ)) (0 : ℝ) :=
        Set.mem_iInter.mp hz
      have hzneg : z < 0 := (hAll 0).2
      have hlim : Tendsto (fun n : ℕ =>
          (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hevent : ∀ᶠ n : ℕ in atTop,
          (1 : ℝ) / ((n + 1 : ℕ) : ℝ) < -z :=
        hlim.eventually_lt_const (by linarith)
      obtain ⟨n, hn⟩ := hevent.exists
      have hzlow : -((1 : ℝ) / ((n + 1 : ℕ) : ℝ)) < z := by
        simpa only [neg_div] using (hAll n).1
      linarith [hzlow, hn]
    · intro hz
      exact False.elim hz
