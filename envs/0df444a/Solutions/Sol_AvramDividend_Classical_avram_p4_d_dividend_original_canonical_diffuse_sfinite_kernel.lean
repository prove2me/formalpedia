-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_canonical_diffuse_sfinite_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T22:04:13.111785+00:00
-- url     : https://prove2.me/submissions/8c380f72-c40f-4f42-9de0-fbe33b881832

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_atomic_support_jointly_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original random dividend measure has a measurable s-finite kernel
that discards exactly the positive-mass singleton atoms, path by path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∃ κdiff : Kernel Ω ℝ,
      IsSFiniteKernel κdiff ∧
      ∀ ω : Ω,
        κdiff ω = (dividendMeasure D ω).restrict
          {t : ℝ | ¬0 < dividendMeasure D ω {t}} := by
  obtain ⟨κ, hκfinite, hκ⟩ := dividendMeasure_global_sfinite_kernel_exists D hD
  letI : IsSFiniteKernel κ := hκfinite
  let f : Ω → ℝ → ℝ≥0∞ := fun ω t =>
    if 0 < dividendMeasure D ω {t} then 0 else 1
  have hgraph :=
    avram_p4_d_dividend_original_random_atomic_support_jointly_measurable D hD
  have hf : Measurable (Function.uncurry f) := by
    exact Measurable.ite hgraph measurable_const measurable_const
  let κdiff : Kernel Ω ℝ := κ.withDensity f
  have hfinite : IsSFiniteKernel κdiff := by
    exact Kernel.IsSFiniteKernel.withDensity κ (by
      intro ω t
      simp only [f]
      split_ifs <;> simp)
  refine ⟨κdiff, hfinite, ?_⟩
  intro ω
  have hs : MeasurableSet
      {t : ℝ | ¬0 < dividendMeasure D ω {t}} := by
    have h := hgraph.compl.preimage
      ((measurable_const : Measurable (fun _ : ℝ => ω)).prodMk measurable_id)
    simpa only [Set.preimage, Set.mem_setOf_eq, Set.mem_compl_iff, id_eq]
      using h
  have hfeq : f ω =
      ({t : ℝ | ¬0 < dividendMeasure D ω {t}} : Set ℝ).indicator
        (fun _ => (1 : ℝ≥0∞)) := by
    funext t
    by_cases ht : 0 < dividendMeasure D ω {t}
    · have hp : dividendMeasure D ω {t} ≠ 0 := ne_of_gt ht
      simp [f, Set.indicator, ht, hp]
    · have hz : dividendMeasure D ω {t} = 0 :=
        le_antisymm (not_lt.mp ht) zero_le
      simp [f, Set.indicator, ht, hz]
  change (κ.withDensity f) ω = _
  rw [Kernel.withDensity_apply κ hf ω, hκ ω, hfeq]
  exact withDensity_indicator_one hs
