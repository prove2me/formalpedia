-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_shrinking_cell_endpoints_common_subseq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:31:54.365663+00:00
-- url     : https://prove2.me/submissions/92eec5c1-fdfe-48cc-9c87-e4f08181bc77

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal

/-- Shrinking original mesh cell endpoints admit a common subsequential time
limit; this is the compactness core of the reverse jump-cell argument. -/
theorem solution
    (T : ℝ≥0) (a b w : ℕ → ℝ≥0)
    (haT : ∀ n, a n ≤ T)
    (hab : ∀ n, a n ≤ b n)
    (hbw : ∀ n, b n ≤ a n + w n)
    (hw : Tendsto w atTop (𝓝 (0 : ℝ≥0))) :
    ∃ t : ℝ≥0, t ∈ Icc (0 : ℝ≥0) T ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n : ℕ => a (φ n)) atTop (𝓝 t) ∧
        Tendsto (fun n : ℕ => b (φ n)) atTop (𝓝 t) := by
  have hc : IsCompact (Icc (0 : ℝ≥0) T) := isCompact_Icc
  have hm : ∀ n, a n ∈ Icc (0 : ℝ≥0) T := by
    intro n
    exact ⟨zero_le, haT n⟩
  obtain ⟨t, ht, φ, hφ, ha⟩ := hc.tendsto_subseq hm
  have hwφ : Tendsto (fun n : ℕ => w (φ n)) atTop (𝓝 (0 : ℝ≥0)) :=
    hw.comp hφ.tendsto_atTop
  have hupper : Tendsto (fun n : ℕ => a (φ n) + w (φ n))
      atTop (𝓝 t) := by
    simpa using ha.add hwφ
  have hb : Tendsto (fun n : ℕ => b (φ n)) atTop (𝓝 t) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le ha hupper
      (fun n => hab (φ n)) (fun n => hbw (φ n))
  exact ⟨t, ht, φ, hφ, ha, hb⟩
