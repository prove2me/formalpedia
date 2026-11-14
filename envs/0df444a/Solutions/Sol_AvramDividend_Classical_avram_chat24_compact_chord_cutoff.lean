-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_compact_chord_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:48:18.931264+00:00
-- url     : https://prove2.me/submissions/de8b3d42-e6ba-4afb-8e25-8800c2c95c6a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (w : ℝ → ℝ) (a b d : ℝ) (B : ℝ≥0) (ha : 0 < a)
    (hw : ContDiffOn ℝ 1 w (Ioi 0)) :
    ∃ n0 : ℕ, ∃ L : ℝ≥0,
      LipschitzOnWith L w (Icc (a / 2) (b + 1)) ∧
      ∀ n : ℕ, n0 ≤ n →
        d * ((B : ℝ) / ((n + 1 : ℕ) : ℝ)) < min (a / 2) 1 := by
  have hpositive : Icc (a / 2) (b + 1) ⊆ Ioi (0 : ℝ) := by
    intro y hy
    exact lt_of_lt_of_le (half_pos ha) hy.1
  obtain ⟨L, hLip⟩ := (hw.mono hpositive).exists_lipschitzOnWith
    (by norm_num) (convex_Icc _ _) isCompact_Icc
  have hmesh : Tendsto (fun n : ℕ => (B : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (nhds 0) :=
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).const_div_atTop (B : ℝ)
  have hδ : Tendsto (fun n : ℕ => d * ((B : ℝ) / ((n + 1 : ℕ) : ℝ)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hmesh
  have heps : 0 < min (a / 2) (1 : ℝ) := lt_min (half_pos ha) zero_lt_one
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp ((tendsto_order.1 hδ).2 _ heps)
  exact ⟨n0, L, hLip, hn0⟩

