-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02a_dense_grid_recovers_separated_source_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:44:22.543983+00:00
-- url     : https://prove2.me/submissions/802afa9b-6df6-42ad-8eda-c8d1f41a0bd8

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Defs.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (s t b : ℝ≥0) (a : ℝ) (hst : s < t) (htb : t < b)
    (hL : ∀ u ∈ Ioo s t, a < X.X u ω)
    (hR : ∀ u ∈ Ico t b, X.X u ω < a) :
    ∃ m : ℕ, grid m ∈ Ioo s t ∧
      (⨅ n : ℕ, {ω : Ω | grid m < grid n ∧ X.X (grid n) ω < a}.piecewise
        (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) ω) = (t : ℝ≥0∞) := by
  classical
  obtain ⟨v, ⟨m, rfl⟩, hm⟩ := hdense.exists_between hst
  refine ⟨m, hm, ?_⟩
  let I : ℝ≥0∞ := ⨅ n : ℕ,
    {ω : Ω | grid m < grid n ∧ X.X (grid n) ω < a}.piecewise
      (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) ω
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
    have hX : X.X (grid n) ω < a := hR (grid n) ⟨le_of_lt hn.1, hnb⟩
    have hI : I ≤ (grid n : ℝ≥0∞) := by
      calc
        I ≤ {ω : Ω | grid m < grid n ∧ X.X (grid n) ω < a}.piecewise
            (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) ω := iInf_le _ n
        _ = (grid n : ℝ≥0∞) := by simp [hmn, hX]
    have hcoe : (grid n : ℝ≥0∞) < (z : ℝ≥0∞) := by exact_mod_cast hnz
    exact (not_lt_of_ge (le_trans hI (le_of_lt hcoe))) hzI
  · apply le_iInf
    intro n
    by_cases h : grid m < grid n ∧ X.X (grid n) ω < a
    · have htn : t ≤ grid n := by
        by_contra hnt
        have hnt' : grid n < t := lt_of_not_ge hnt
        have hAbove := hL (grid n) ⟨lt_trans hm.1 h.1, hnt'⟩
        exact (not_lt_of_ge (le_of_lt hAbove)) h.2
      simpa [h] using (show (t : ℝ≥0∞) ≤ (grid n : ℝ≥0∞) by exact_mod_cast htn)
    · simp [h]
