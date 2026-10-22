-- Prove2me | solution 1 for AvramDividend.Classical.chat03_noexit_sampled_clock_caps_to_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T14:59:31.707582+00:00
-- url     : https://prove2.me/submissions/aa9d22c6-60ec-4a1b-af98-35e7130a1849

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_hittingBtwn_eq_terminal_of_no_observed_crossing
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
On a path with no strict exit through the terminal grid time, the
genuine bounded hittingBtwn clock capped at an earlier horizon equals it.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ)
    (mesh T : ℝ≥0) (m : ℕ)
    (hT : T ≤ (m : ℝ≥0) * mesh)
    (hNo : ∀ t : ℝ≥0, t ≤ (m : ℝ≥0) * mesh →
      ¬ (X.X t ω < lower ∨ upper < X.X t ω)) :
    min (((hittingBtwn
        (fun (j : ℕ) ξ => max
          (X.X ((j : ℝ≥0) * mesh) ξ - upper)
          (lower - X.X ((j : ℝ≥0) * mesh) ξ))
        (Set.Ioi (0 : ℝ)) 0 m ω : ℕ) : ℝ≥0) * mesh) T = T := by
  have hnone (j : ℕ) (hj : j < m) :
      max (X.X ((j : ℝ≥0) * mesh) ω - upper)
        (lower - X.X ((j : ℝ≥0) * mesh) ω) ∉ Set.Ioi (0 : ℝ) := by
    have hjle : (j : ℝ≥0) * mesh ≤ (m : ℝ≥0) * mesh :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.le_of_lt hj))
        (show (0 : ℝ≥0) ≤ mesh from zero_le)
    have hnot := hNo ((j : ℝ≥0) * mesh) hjle
    intro hmem
    have hcase :
        upper < X.X ((j : ℝ≥0) * mesh) ω ∨
          X.X ((j : ℝ≥0) * mesh) ω < lower := by
      simpa only [Set.mem_Ioi, lt_max_iff, sub_pos] using hmem
    exact hnot hcase.symm
  have hclock :
      hittingBtwn
        (fun (j : ℕ) ξ => max
          (X.X ((j : ℝ≥0) * mesh) ξ - upper)
          (lower - X.X ((j : ℝ≥0) * mesh) ξ))
        (Set.Ioi (0 : ℝ)) 0 m ω = m :=
    chat03_hittingBtwn_eq_terminal_of_no_observed_crossing
      _ _ ω m hnone
  simp [hclock, min_eq_right hT]
