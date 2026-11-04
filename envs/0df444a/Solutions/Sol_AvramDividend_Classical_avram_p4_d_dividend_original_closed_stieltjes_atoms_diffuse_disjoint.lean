-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_closed_stieltjes_atoms_diffuse_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:39:22.620874+00:00
-- url     : https://prove2.me/submissions/8fce7a70-1b12-4484-94c3-c8fd942de851

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original closed Stieltjes cash has non-overlapping right-atomic and
diffuse carriers, with zero and horizon right atoms and exact total mass. -/
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
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      μ Set.univ = ENNReal.ofReal (rightLimit D T ω) := by
  let μ : Measure ℝ :=
    (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  change ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
    A.Countable ∧ MeasurableSet A ∧
    μ = μatom + μdiffuse ∧
    NullSingletonClass μdiffuse ∧
    μatom Aᶜ = 0 ∧ μdiffuse A = 0 ∧
    (∀ t : ℝ≥0, t ≤ T →
      μ {(t : ℝ)} =
        ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
    μ Set.univ = ENNReal.ofReal (rightLimit D T ω)
  obtain ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit,
      _hAtoms, hAtomCompl, hNull, hSingleton, hMass⟩ :=
    avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse
      D hD ω T
  haveI : NullSingletonClass μdiffuse := hNull
  refine ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit,
    hNull, hAtomCompl, ?_, hSingleton, hMass⟩
  exact hCount.measure_zero μdiffuse