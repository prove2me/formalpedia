-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_path_dense_grid_any_prior_start_exact_downcrossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:56:11.908198+00:00
-- url     : https://prove2.me/submissions/b9d26b85-0c58-44fc-81c4-41dedd57273d

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- The exact infimum of a separated downcrossing is independent of which grid start precedes the jump. -/
theorem solution
    (Y : ℝ≥0 → ℝ)
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (s t b : ℝ≥0) (a : ℝ) (hst : s < t) (htb : t < b)
    (hL : ∀ u ∈ Ioo s t, a < Y u)
    (hR : ∀ u ∈ Ico t b, Y u < a) :
    ∀ m : ℕ, grid m ∈ Ioo s t →
      (⨅ n : ℕ,
        {Z : ℝ≥0 → ℝ | grid m < grid n ∧ Z (grid n) < a}.piecewise
          (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) Y) =
      (t : ℝ≥0∞) := by
  classical
  intro m hm
  let I : ℝ≥0∞ := ⨅ n : ℕ,
    {Z : ℝ≥0 → ℝ | grid m < grid n ∧ Z (grid n) < a}.piecewise
      (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) Y
  change I = (t : ℝ≥0∞)
  apply le_antisymm
  · by_contra h
    have htI : (t : ℝ≥0∞) < I := lt_of_not_ge h
    obtain ⟨z, htz, hzI⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp htI
    have htz' : t < z := by exact_mod_cast htz
    have htmin : t < min b z := lt_min htb htz'
    obtain ⟨v, ⟨n, rfl⟩, hn⟩ := hdense.exists_between htmin
    have hmn : grid m < grid n := lt_trans hm.2 hn.1
    have hnb : grid n < b := lt_of_lt_of_le hn.2 (min_le_left b z)
    have hnz : grid n < z := lt_of_lt_of_le hn.2 (min_le_right b z)
    have hY : Y (grid n) < a := hR (grid n) ⟨le_of_lt hn.1, hnb⟩
    have hI : I ≤ (grid n : ℝ≥0∞) := by
      calc
        I ≤ {Z : ℝ≥0 → ℝ | grid m < grid n ∧ Z (grid n) < a}.piecewise
            (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) Y := iInf_le _ n
        _ = (grid n : ℝ≥0∞) := by simp [hmn, hY]
    have hcoe : (grid n : ℝ≥0∞) < (z : ℝ≥0∞) := by exact_mod_cast hnz
    exact (not_lt_of_ge (le_trans hI (le_of_lt hcoe))) hzI
  · apply le_iInf
    intro n
    by_cases h : grid m < grid n ∧ Y (grid n) < a
    · have htn : t ≤ grid n := by
        by_contra hnt
        have hnt' : grid n < t := lt_of_not_ge hnt
        have hAbove := hL (grid n) ⟨lt_trans hm.1 h.1, hnt'⟩
        exact (not_lt_of_ge (le_of_lt hAbove)) h.2
      simpa [h] using
        (show (t : ℝ≥0∞) ≤ (grid n : ℝ≥0∞) by exact_mod_cast htn)
    · simp [h]
