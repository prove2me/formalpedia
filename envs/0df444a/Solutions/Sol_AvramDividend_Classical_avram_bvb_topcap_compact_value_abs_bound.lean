-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_topcap_compact_value_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T07:42:09.375051+00:00
-- url     : https://prove2.me/submissions/8f6c0349-9d77-442b-90d7-5191c7ee8102

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger63_compact_continuous_value_finite_lower_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0)) (B : ℝ) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b : ℝ, 0 ≤ b → b ≤ B → |w b| ≤ K := by
  have hsubset : Icc (0 : ℝ) B ⊆ Ici (0 : ℝ) := by
    intro y hy
    exact hy.1
  have hwI : ContinuousOn w (Icc (0 : ℝ) B) := hw.mono hsubset
  obtain ⟨L, hL0, hL⟩ :=
    AvramDividend.Classical.avram_gledger63_compact_continuous_value_finite_lower_bound
      0 B hB w hwI
  have hwNeg : ContinuousOn (fun y : ℝ => -w y) (Icc (0 : ℝ) B) :=
    hwI.neg
  obtain ⟨U, hU0, hU⟩ :=
    AvramDividend.Classical.avram_gledger63_compact_continuous_value_finite_lower_bound
      0 B hB (fun y : ℝ => -w y) hwNeg
  refine ⟨L + U, add_nonneg hL0 hU0, ?_⟩
  intro y hy0 hyB
  have hlo := hL y hy0 hyB
  have hhi := hU y hy0 hyB
  exact abs_le.mpr ⟨by linarith, by linarith⟩
