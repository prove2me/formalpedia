-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_NX_ae_negative_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:17:28.886393+00:00
-- url     : https://prove2.me/submissions/e09c207d-0493-43f7-a2f1-2bd0ca9930ff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_intrinsic_marked_measure_global_nonnegative_support_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    ∀ᵐ p ∂((Measure.count.restrict
      {s : ℝ≥0 | 0 < s ∧ X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
      (fun s : ℝ≥0 => (s, X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s))),
      p.2 < (0 : ℝ) := by
  rw [ae_iff]
  have hZero :=
    AvramDividend.Classical.avram_wave5_01_actual_intrinsic_marked_measure_global_nonnegative_support_zero
      X ω
  convert hZero using 1
  congr 1
  ext p
  simp [Set.mem_prod, not_lt]

