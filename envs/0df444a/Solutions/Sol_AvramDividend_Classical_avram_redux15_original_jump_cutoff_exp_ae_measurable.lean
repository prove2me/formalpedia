-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux15_original_jump_cutoff_exp_ae_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T11:31:52.381888+00:00
-- url     : https://prove2.me/submissions/a5522638-0f32-4d78-a20f-41268e428cdc

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- Measurability of the actual original cutoff jump exponential. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ (n k : ℕ),
      AEStronglyMeasurable (fun ω : Ω => Real.exp (-((∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) ∧
          (1 / ((k : ℝ) + 1)) < (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω) then
          ENNReal.ofReal
            (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal))) P := by
  intro n k
  obtain ⟨κ, _, hκ⟩ := avram_wave5_02a_actual_source_intrinsic_sfinite_kernel X
  let F : (ℝ≥0 × ℝ) → ℝ≥0∞ := fun p =>
    if 0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) ∧ (1 / ((k : ℝ) + 1)) < -p.2
    then ENNReal.ofReal (-p.2) else 0
  have hF : Measurable F := by
    dsimp [F]
    apply Measurable.ite
      ((measurableSet_lt measurable_const measurable_fst).inter
        ((measurableSet_le measurable_fst measurable_const).inter
          (measurableSet_lt measurable_const measurable_snd.neg)))
    · exact ENNReal.measurable_ofReal.comp measurable_snd.neg
    · exact measurable_const
  have hK : Measurable (fun ω : Ω => Real.exp (-((∫⁻ p, F p ∂κ ω).toReal))) :=
    Real.measurable_exp.comp
      (ENNReal.measurable_toReal.comp (Measurable.lintegral_kernel hF)).neg
  have hEq (ω : Ω) :
      (∑' v : ℝ≥0,
        if 0 < v ∧ v ≤ (n : ℝ≥0) ∧
          (1 / ((k : ℝ) + 1)) < (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        then ENNReal.ofReal
          (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0) = ∫⁻ p, F p ∂κ ω := by
    rw [hκ ω, avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum X ω F hF]
    apply tsum_congr
    intro v
    let L := Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
    change (if 0 < v ∧ v ≤ (n : ℝ≥0) ∧
        (1 / ((k : ℝ) + 1)) < L - X.X v ω then ENNReal.ofReal (L - X.X v ω) else 0) =
      (if 0 < v ∧ X.X v ω - L ≠ 0 then F (v, X.X v ω - L) else 0)
    by_cases hc : 0 < v ∧ v ≤ (n : ℝ≥0) ∧ (1 / ((k : ℝ) + 1)) < L - X.X v ω
    · have hj : X.X v ω - L ≠ 0 := by
        intro hz
        have hp : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith [hc.2.2]
      simp [F, hc, hj, neg_sub]
    · by_cases hj : 0 < v ∧ X.X v ω - L ≠ 0
      · simp [F, hc, hj, neg_sub]
      · simp only [if_neg hc, if_neg hj]
  have hFun : (fun ω : Ω => Real.exp (-((∑' v : ℝ≥0,
      if 0 < v ∧ v ≤ (n : ℝ≥0) ∧
        (1 / ((k : ℝ) + 1)) < (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
      then ENNReal.ofReal
        (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
      else 0).toReal))) =
      (fun ω : Ω => Real.exp (-((∫⁻ p, F p ∂κ ω).toReal))) := by
    funext ω
    rw [hEq ω]
  rw [hFun]
  exact hK.aestronglyMeasurable
