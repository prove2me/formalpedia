-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T07:34:45.006756+00:00
-- url     : https://prove2.me/submissions/be2d4e3f-7600-4a04-813e-c9c35c03e59a

import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Original marked negative-jump counts are measurable for random physical endpoints. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (cut : ℕ) (τ e : Ω → ℝ≥0)
    (hτ : Measurable τ) (he : Measurable e) :
    Measurable (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (τ ω) (e ω) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))) := by
  classical
  obtain ⟨κ, hκs, hκX⟩ :=
    avram_wave5_02a_actual_source_intrinsic_sfinite_kernel X
  letI : IsSFiniteKernel κ := hκs
  let S : Set (Ω × (ℝ≥0 × ℝ)) :=
    {p | (τ p.1 < p.2.1 ∧ p.2.1 ≤ e p.1) ∧
      p.2.2 ≤ -(1 / ((cut : ℝ) + 1))}
  have hTau : Measurable (fun p : Ω × (ℝ≥0 × ℝ) => τ p.1) :=
    hτ.comp measurable_fst
  have hEnd : Measurable (fun p : Ω × (ℝ≥0 × ℝ) => e p.1) :=
    he.comp measurable_fst
  have hTime : Measurable (fun p : Ω × (ℝ≥0 × ℝ) => p.2.1) :=
    measurable_fst.comp measurable_snd
  have hMark : Measurable (fun p : Ω × (ℝ≥0 × ℝ) => p.2.2) :=
    measurable_snd.comp measurable_snd
  have hS : MeasurableSet S := by
    change MeasurableSet
      ({p : Ω × (ℝ≥0 × ℝ) | τ p.1 < p.2.1} ∩
       {p | p.2.1 ≤ e p.1} ∩
       {p | p.2.2 ≤ -(1 / ((cut : ℝ) + 1))})
    exact ((measurableSet_lt hTau hTime).inter
      (measurableSet_le hTime hEnd)).inter
      (measurableSet_le hMark measurable_const)
  have hSet (ω : Ω) :
      (Prod.mk ω) ⁻¹' S =
        Ioc (τ ω) (e ω) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))) := by
    ext p
    simp [S, Set.mem_prod, Set.mem_Ioc, Set.mem_Iic]
  have hM : Measurable (fun ω : Ω =>
      (κ ω) ((Prod.mk ω) ⁻¹' S)) :=
    ProbabilityTheory.Kernel.measurable_kernel_prodMk_left hS
  simpa only [hκX, hSet] using hM
