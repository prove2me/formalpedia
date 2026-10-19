-- Prove2me | solution 1 for AvramDividend.Classical.prepeak_reflected_ruin_hitting_time_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T06:24:11.009706+00:00
-- url     : https://prove2.me/submissions/f8c2738e-423a-41b9-b112-e919b8704f2b

import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.CompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_drawdown_strict_exit_strip_of_sup_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal

theorem solution
    (I : Set ℝ≥0) (S X : ℝ≥0 → ℝ) (a h : ℝ)
    (hSup : ∀ t ∈ I, 0 ≤ S t ∧ S t ≤ h) :
    sInf (Set.image (fun t : ℝ≥0 => (t : ℝ≥0∞))
      {t : ℝ≥0 | t ∈ I ∧ X t < h - a}) ≤
    sInf (Set.image (fun t : ℝ≥0 => (t : ℝ≥0∞))
      {t : ℝ≥0 | t ∈ I ∧ a < S t - X t}) ∧
    sInf (Set.image (fun t : ℝ≥0 => (t : ℝ≥0∞))
      {t : ℝ≥0 | t ∈ I ∧ a < S t - X t}) ≤
    sInf (Set.image (fun t : ℝ≥0 => (t : ℝ≥0∞))
      {t : ℝ≥0 | t ∈ I ∧ X t < -a}) := by
  have hLower :
      {t : ℝ≥0 | t ∈ I ∧ X t < -a} ⊆
      {t : ℝ≥0 | t ∈ I ∧ a < S t - X t} := by
    intro t ht
    have hs := hSup t ht.1
    have hStrip :=
      AvramDividend.Classical.drawdown_strict_exit_strip_of_sup_bounds
        a h (S t) (X t) hs.1 hs.2
    exact ⟨ht.1, hStrip.1 ht.2⟩
  have hUpper :
      {t : ℝ≥0 | t ∈ I ∧ a < S t - X t} ⊆
      {t : ℝ≥0 | t ∈ I ∧ X t < h - a} := by
    intro t ht
    have hs := hSup t ht.1
    have hStrip :=
      AvramDividend.Classical.drawdown_strict_exit_strip_of_sup_bounds
        a h (S t) (X t) hs.1 hs.2
    exact ⟨ht.1, hStrip.2.1 ht.2⟩
  constructor
  · exact sInf_le_sInf (Set.image_mono hUpper)
  · exact sInf_le_sInf (Set.image_mono hLower)
