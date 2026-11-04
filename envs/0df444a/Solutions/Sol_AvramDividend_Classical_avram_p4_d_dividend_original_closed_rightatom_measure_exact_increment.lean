-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_closed_rightatom_measure_exact_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:31:43.143702+00:00
-- url     : https://prove2.me/submissions/5133d8e2-6182-4502-ac6f-b9752cd175df

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_stieltjes_atoms_diffuse_disjoint
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original right-payment atom belongs entirely to the atomic Stieltjes measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      NullSingletonClass μdiffuse ∧
      μatom Aᶜ = 0 ∧ μdiffuse A = 0 ∧
      μ Set.univ = ENNReal.ofReal (rightLimit D T ω) ∧
      (∀ t : ℝ≥0, t ≤ T →
        μatom {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) := by
  obtain ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit,
      hNull, hAtomOutside, hDiffCarrier, hSingleton, hMass⟩ :=
    avram_p4_d_dividend_original_closed_stieltjes_atoms_diffuse_disjoint D hD ω T
  refine ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit,
    hNull, hAtomOutside, hDiffCarrier, hMass, ?_⟩
  letI : NullSingletonClass μdiffuse := hNull
  intro t ht
  have hSource := hSingleton t ht
  rw [hSplit] at hSource
  simpa using hSource
