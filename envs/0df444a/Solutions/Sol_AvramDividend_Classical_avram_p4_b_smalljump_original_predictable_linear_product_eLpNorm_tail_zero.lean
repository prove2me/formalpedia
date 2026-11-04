-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_linear_product_eLpNorm_tail_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:16:56.48182+00:00
-- url     : https://prove2.me/submissions/a0116170-8e23-4656-9fa7-696ce196e8e5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_small_negative_linear_mark_MemLp
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_linear_L2_thinning_tail_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True original predictable small-negative linear jump bands tend to zero
in the complete eLpNorm L2 seminorm, not merely their raw square energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (g : ℝ≥0 × Ω → ℝ)
    (hgm : Measurable[𝓕.rightCont.predictable] g)
    (hgL2 : (∫⁻ p : ℝ≥0 × Ω,
      ENNReal.ofReal ((g p)^2) ∂μ) < ⊤)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Tendsto (fun n : ℕ =>
        eLpNorm
          (({r : ((ℝ≥0 × Ω) × ℝ) | r.2 ∈ B n}).indicator
            (fun r : ((ℝ≥0 × Ω) × ℝ) => g r.1 * r.2))
          (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))
        atTop (𝓝 0)) := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  let M : Measure ((ℝ≥0 × Ω) × ℝ) :=
    μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))
  let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun r => g r.1 * r.2
  let A : ℕ → Set ((ℝ≥0 × Ω) × ℝ) := fun n => {r | r.2 ∈ B n}
  have hML : MemLp G (2 : ℝ≥0∞) M :=
    avram_p4_b_smalljump_original_small_negative_linear_mark_MemLp
      X μ g hgm hgL2
  have hA (n : ℕ) : MeasurableSet (A n) :=
    (hBm n).preimage measurable_snd
  have hEnergy := avram_p4_b_smalljump_original_predictable_linear_L2_thinning_tail_zero
    X μ g hgm hgL2 B hBm hBanti hBempty
  have hNorm (n : ℕ) :
      eLpNorm ((A n).indicator G) (2 : ℝ≥0∞) M =
        (∫⁻ r, (A n).indicator (fun p => ENNReal.ofReal ((g p.1 * p.2)^2)) r ∂M)
          ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal]
    norm_num
    congr 1
    apply lintegral_congr
    intro r
    by_cases hr : r ∈ A n
    · simp only [Set.indicator_of_mem hr]
      rw [Real.enorm_eq_ofReal_abs,
        ← ENNReal.ofReal_pow (abs_nonneg (G r)) 2, sq_abs]
    · simp only [Set.indicator_of_notMem hr]
      norm_num
    all_goals try norm_num
    all_goals try exact (hML.indicator (hA n)).aestronglyMeasurable
  have hRoot := hEnergy.ennrpow_const (1 / 2 : ℝ)
  have hGoal : Tendsto (fun n : ℕ =>
      eLpNorm ((A n).indicator G) (2 : ℝ≥0∞) M) atTop (𝓝 0) := by
    convert hRoot using 1
    · funext n
      exact hNorm n
    · norm_num
  exact hGoal
