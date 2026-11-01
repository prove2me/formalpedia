-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_weighted_time_measure_le_source_stieltjes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:25:19.509345+00:00
-- url     : https://prove2.me/submissions/e412d397-c03d-4fe4-af78-12d287b80c80

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_jump_atomic_domination_all_measurable_time_sets

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ F : StieltjesFunction ℝ≥0,
      (∀ t : ℝ≥0, (F t : ℝ) = (t : ℝ) * X.drift - X.X t ω) ∧
      (∀ (B : Set ℝ≥0), MeasurableSet B →
        (∫⁻ p,
          (if p.1 ∈ B then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ≤
        F.measure B) := by
  filter_upwards
    [avram_wave4_04a_bv_actual_jump_atomic_domination_all_measurable_time_sets X hBV]
    with ω hω
  obtain ⟨F, hF, hdom⟩ := hω
  refine ⟨F, hF, ?_⟩
  intro B hB
  classical
  have hmeas :
      Measurable (fun p : ℝ≥0 × ℝ =>
        if p.1 ∈ B then ENNReal.ofReal (-p.2) else 0) := by
    apply Measurable.ite (hB.preimage measurable_fst)
    · exact ENNReal.measurable_ofReal.comp (measurable_snd.neg)
    · exact measurable_const
  rw [avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum X ω
    (fun p : ℝ≥0 × ℝ =>
      if p.1 ∈ B then ENNReal.ofReal (-p.2) else 0) hmeas]
  calc
    (∑' u : ℝ≥0,
      if 0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 then
        (if u ∈ B then
          ENNReal.ofReal (-(X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) else 0)
      else 0) =
      (∑' u : ℝ≥0,
        if 0 < u ∧ u ∈ B then
          ENNReal.ofReal (Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
        else 0) := by
        apply tsum_congr
        intro u
        by_cases hpos : 0 < u
        · by_cases hbu : u ∈ B
          · by_cases hmark :
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u = 0
            · have hzero : Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u - X.X u ω = 0 := by
                linarith
              simp [hpos, hbu, hmark, hzero]
            · simpa [hpos, hbu, hmark, neg_sub]
          · simp [hbu]
        · simp [hpos]
    _ ≤ _ := hdom B hB
