-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger98_original_random_strict_open_mass_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:22:21.130583+00:00
-- url     : https://prove2.me/submissions/f1e724e8-fda8-496f-bd04-b6b47132d70f

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Kernel measurability of the original dividend Stieltjes mass before a random clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (hρ : Measurable ρ) :
    Measurable (fun ω : Ω =>
      dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))) := by
  classical
  let A : Set (ℝ × Ω) := {p | 0 < p.1 ∧ p.1 < (ρ p.2 : ℝ)}
  have hA : MeasurableSet A :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst
        (hρ.coe_nnreal_real.comp measurable_snd))
  obtain ⟨κ, hκs, hκ⟩ :=
    dividendMeasure_global_sfinite_kernel_exists D hD
  letI : IsSFiniteKernel κ := hκs
  have hKernel := measurable_random_indicator_lintegral κ A hA
    (fun _ : ℝ => (1 : ℝ≥0∞)) measurable_const
  have hEq :
      (fun ω : Ω => dividendMeasure D ω (Ioo 0 (ρ ω : ℝ))) =
      (fun ω : Ω => ∫⁻ t, if (t, ω) ∈ A then (1 : ℝ≥0∞) else 0 ∂κ ω) := by
    funext ω
    have hI : MeasurableSet (Ioo (0 : ℝ) (ρ ω : ℝ)) := measurableSet_Ioo
    calc
      dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ)) =
          ∫⁻ t in Ioo (0 : ℝ) (ρ ω : ℝ), (1 : ℝ≥0∞) ∂dividendMeasure D ω := by simp
      _ = ∫⁻ t, if (t, ω) ∈ A then (1 : ℝ≥0∞) else 0 ∂κ ω := by
        rw [hκ ω, ← lintegral_indicator hI (fun _ : ℝ => (1 : ℝ≥0∞))]
        apply lintegral_congr
        intro t
        by_cases ht : t ∈ Ioo (0 : ℝ) (ρ ω : ℝ)
        · have htA : (t, ω) ∈ A := ht
          simp [Set.indicator, ht, htA]
        · have htA : (t, ω) ∉ A := fun hs => ht hs
          simp [Set.indicator, ht, htA]
  rw [hEq]
  simpa only [A, Set.mem_setOf_eq] using hKernel
