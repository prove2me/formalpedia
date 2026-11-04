-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_discounted_closed_atomic_diffuse_cash_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:18:31.692389+00:00
-- url     : https://prove2.me/submissions/7751313e-f3d9-4f6d-ba1a-d33f7d2c6ea4

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_stieltjes_atoms_diffuse_disjoint
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_restrict_cash_eq_literal_stop
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Original stopped dividend Cash splits exactly into disjoint right-atomic and diffuse discounted Stieltjes contributions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    let f : ℝ → ℝ≥0∞ := fun s =>
      if s ∈ paymentTimes (ruinTime X x D ω)
      then ENNReal.ofReal (Real.exp (-(q * s))) else 0
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      NullSingletonClass μdiffuse ∧
      μatom Aᶜ = 0 ∧ μdiffuse A = 0 ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      μ Set.univ = ENNReal.ofReal (rightLimit D T ω) ∧
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) =
        (∫⁻ s : ℝ, f s ∂μatom) + (∫⁻ s : ℝ, f s ∂μdiffuse) := by
  obtain ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit,
      hNull, hAtomOutside, hDiffCarrier, hSingleton, hMass⟩ :=
    avram_p4_d_dividend_original_closed_stieltjes_atoms_diffuse_disjoint D hD ω T
  refine ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit,
    hNull, hAtomOutside, hDiffCarrier, hSingleton, hMass, ?_⟩
  let f : ℝ → ℝ≥0∞ := fun s =>
    if s ∈ paymentTimes (ruinTime X x D ω)
    then ENNReal.ofReal (Real.exp (-(q * s))) else 0
  have hCash :=
    avram_p4_d_dividend_original_closed_restrict_cash_eq_literal_stop
      X x D hD q ω T
  calc
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) =
        (∫⁻ s : ℝ, f s ∂((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)))) := by
          exact hCash.symm
    _ = (∫⁻ s : ℝ, f s ∂μatom) + (∫⁻ s : ℝ, f s ∂μdiffuse) := by
      rw [hSplit]
      exact MeasureTheory.lintegral_add_measure f μatom μdiffuse
