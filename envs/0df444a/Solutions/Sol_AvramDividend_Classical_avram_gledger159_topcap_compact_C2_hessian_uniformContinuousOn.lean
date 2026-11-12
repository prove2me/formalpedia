-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger159_topcap_compact_C2_hessian_uniformContinuousOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T21:06:13.688331+00:00
-- url     : https://prove2.me/submissions/9d5e777e-f695-491c-b5fa-6c787ade0db9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    UniformContinuousOn (iteratedDeriv 2 w) (Icc a b) := by
  let U : Set ℝ := {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}
  have hopen : IsOpen U := by
    exact isOpen_Ioi.inter (isOpen_Iio.preimage ENNReal.continuous_ofReal)
  have hsub : Icc a b ⊆ U := by
    intro y hy
    exact ⟨lt_of_lt_of_le ha hy.1, by simp [hTopCap]⟩
  have hu : UniqueDiffOn ℝ U := hopen.uniqueDiffOn
  have hc : ContinuousOn (iteratedDerivWithin 2 w U) U :=
    hw.continuousOn_iteratedDerivWithin (by norm_num) hu
  have heq : EqOn (iteratedDerivWithin 2 w U) (iteratedDeriv 2 w) U :=
    iteratedDerivWithin_of_isOpen hopen
  have hc2 : ContinuousOn (iteratedDeriv 2 w) (Icc a b) :=
    (hc.congr heq.symm).mono hsub
  exact isCompact_Icc.uniformContinuousOn_of_continuous hc2
