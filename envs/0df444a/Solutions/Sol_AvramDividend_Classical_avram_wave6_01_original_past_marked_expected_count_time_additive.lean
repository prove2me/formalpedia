-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_past_marked_expected_count_time_additive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:19:42.256794+00:00
-- url     : https://prove2.me/submissions/873e6e79-7594-4d79-a39a-20a1cc8ac269

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_intrinsic_jump_count_time_interval_additive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s u t : ℝ≥0) (hsu : s ≤ u) (hut : u ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {v : ℝ≥0 |
        0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
        (fun v : ℝ≥0 => (v, X.X v ω -
          Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
        (Ioc s t ×ˢ B) ∂P) =
    (∫⁻ ω in A,
      ((Measure.count.restrict {v : ℝ≥0 |
        0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
        (fun v : ℝ≥0 => (v, X.X v ω -
          Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
        (Ioc s u ×ˢ B) ∂P) +
    (∫⁻ ω in A,
      ((Measure.count.restrict {v : ℝ≥0 |
        0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
        (fun v : ℝ≥0 => (v, X.X v ω -
          Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
        (Ioc u t ×ˢ B) ∂P) := by
  classical
  let N : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    (Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v, X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))
  obtain ⟨κ, hκFinite, hκ⟩ :=
    avram_wave5_02a_actual_source_intrinsic_sfinite_kernel X
  have hSetB : MeasurableSet (Ioc s u ×ˢ B) :=
    measurableSet_Ioc.prod hB
  have hMeas : Measurable (fun ω => N ω (Ioc s u ×ˢ B)) := by
    have hk := ProbabilityTheory.Kernel.measurable_coe κ hSetB
    convert hk using 1
    funext ω
    exact congrArg (fun μ : Measure (ℝ≥0 × ℝ) => μ (Ioc s u ×ˢ B)) (hκ ω).symm
  have hPoint (ω : Ω) :
      N ω (Ioc s t ×ˢ B) =
        N ω (Ioc s u ×ˢ B) + N ω (Ioc u t ×ˢ B) :=
    avram_wave5_01_actual_source_intrinsic_jump_count_time_interval_additive
      X ω s u t hsu hut B hB
  change (∫⁻ ω in A, N ω (Ioc s t ×ˢ B) ∂P) =
    (∫⁻ ω in A, N ω (Ioc s u ×ˢ B) ∂P) +
    (∫⁻ ω in A, N ω (Ioc u t ×ˢ B) ∂P)
  calc
    (∫⁻ ω in A, N ω (Ioc s t ×ˢ B) ∂P) =
        ∫⁻ ω in A, (N ω (Ioc s u ×ˢ B) +
          N ω (Ioc u t ×ˢ B)) ∂P := by
        apply lintegral_congr
        intro ω
        exact hPoint ω
    _ = _ := lintegral_add_left hMeas _
