-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_actual_jump_total_aemeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:51:23.719772+00:00
-- url     : https://prove2.me/submissions/9e9d9a2f-0bd4-4552-9ba7-da6166458e32

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The actual original negative-jump total is almost-everywhere measurable,
using the source s-finite jump kernel and intrinsic jump encoding. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) :
    AEMeasurable (fun ω : Ω =>
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ T then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal) P := by
  classical
  obtain ⟨κ, _, hκ⟩ :=
    avram_wave5_02a_actual_source_intrinsic_sfinite_kernel X
  let F : (ℝ≥0 × ℝ) → ℝ≥0∞ := fun p =>
    if 0 < p.1 ∧ p.1 ≤ T then ENNReal.ofReal (-p.2) else 0
  have hF : Measurable F := by
    dsimp [F]
    apply Measurable.ite
      ((measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_le measurable_fst measurable_const))
    · exact ENNReal.measurable_ofReal.comp (measurable_snd.neg)
    · exact measurable_const
  have hKernelMeas : Measurable (fun ω : Ω =>
      (∫⁻ p, F p ∂κ ω).toReal) :=
    ENNReal.measurable_toReal.comp (Measurable.lintegral_kernel hF)
  have hSource := avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure X hBV
  have hEq : (fun ω : Ω =>
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ T then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal) =ᵐ[P]
      (fun ω : Ω => (∫⁻ p, F p ∂κ ω).toReal) := by
    filter_upwards [hSource] with ω hω
    calc
      (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal =
        (∫⁻ p, F p ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal := by
          simpa only [F] using hω T
      _ = (∫⁻ p, F p ∂κ ω).toReal := by rw [hκ ω]
  exact hKernelMeas.aemeasurable.congr hEq.symm
