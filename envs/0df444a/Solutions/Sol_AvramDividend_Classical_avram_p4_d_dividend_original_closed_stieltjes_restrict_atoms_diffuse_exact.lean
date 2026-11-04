-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_closed_stieltjes_restrict_atoms_diffuse_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:46:24.745948+00:00
-- url     : https://prove2.me/submissions/e3fa8fa2-db1e-4ef4-bb38-72cf3fb9ab5d

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact restriction of the original source closed Stieltjes measure to
right-payment atoms and all complementary diffuse (including singular) mass. -/
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
      μ.restrict A = μatom ∧
      μ.restrict Aᶜ = μdiffuse ∧
      NullSingletonClass μdiffuse ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      μ Set.univ = ENNReal.ofReal (rightLimit D T ω) := by
  let μ : Measure ℝ :=
    (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  change ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
    A.Countable ∧ MeasurableSet A ∧
    μ = μatom + μdiffuse ∧
    μ.restrict A = μatom ∧
    μ.restrict Aᶜ = μdiffuse ∧
    NullSingletonClass μdiffuse ∧
    (∀ t : ℝ≥0, t ≤ T →
      μ {(t : ℝ)} =
        ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
    μ Set.univ = ENNReal.ofReal (rightLimit D T ω)
  obtain ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit,
      _hAtoms, hAtomCompl, hNull, hSingleton, hMass⟩ :=
    avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse
      D hD ω T
  change μ = μatom + μdiffuse at hSplit
  haveI : NullSingletonClass μdiffuse := hNull
  have hDiffuseA : μdiffuse A = 0 :=
    hCount.measure_zero μdiffuse
  have hAtomAE : ∀ᵐ z ∂μatom, z ∈ A := by
    change A ∈ ae μatom
    exact (mem_ae_iff).2 hAtomCompl
  have hDiffuseAE : ∀ᵐ z ∂μdiffuse, z ∈ Aᶜ := by
    change Aᶜ ∈ ae μdiffuse
    exact (mem_ae_iff).2 (by simpa only [compl_compl] using hDiffuseA)
  have hAtomRestr : μatom.restrict A = μatom :=
    Measure.restrict_eq_self_of_ae_mem hAtomAE
  have hDiffuseRestr : μdiffuse.restrict Aᶜ = μdiffuse :=
    Measure.restrict_eq_self_of_ae_mem hDiffuseAE
  have hAtomZero : μatom.restrict Aᶜ = 0 :=
    Measure.restrict_eq_zero.mpr hAtomCompl
  have hDiffuseZero : μdiffuse.restrict A = 0 :=
    Measure.restrict_eq_zero.mpr hDiffuseA
  have hExactAtom : μ.restrict A = μatom := by
    rw [hSplit, Measure.restrict_add, hAtomRestr, hDiffuseZero, add_zero]
  have hExactDiffuse : μ.restrict Aᶜ = μdiffuse := by
    rw [hSplit, Measure.restrict_add, hAtomZero, hDiffuseRestr, zero_add]
  exact ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit,
    hExactAtom, hExactDiffuse, hNull, hSingleton, hMass⟩