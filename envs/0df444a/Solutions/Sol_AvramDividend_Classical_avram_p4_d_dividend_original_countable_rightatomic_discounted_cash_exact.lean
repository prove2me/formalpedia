-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_countable_rightatomic_discounted_cash_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:30:56.080544+00:00
-- url     : https://prove2.me/submissions/70d8173b-e3cd-4630-b83e-5959d3542c9d

import Mathlib
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

/-- Exact original closed-window Cash equals a countable right-atom sum plus diffuse Cash. -/
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
        (∑' a : A, f a.1 * μatom {a.1}) +
          (∫⁻ s : ℝ, f s ∂μdiffuse) := by
  obtain ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit,
      hNull, hAtomOutside, hDiffCarrier, hSingleton, hMass⟩ :=
    avram_p4_d_dividend_original_closed_stieltjes_atoms_diffuse_disjoint D hD ω T
  refine ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit,
    hNull, hAtomOutside, hDiffCarrier, hSingleton, hMass, ?_⟩
  let f : ℝ → ℝ≥0∞ := fun s =>
    if s ∈ paymentTimes (ruinTime X x D ω)
    then ENNReal.ofReal (Real.exp (-(q * s))) else 0
  have hAE : ∀ᵐ s ∂μatom, s ∈ A := by
    exact ae_iff.mpr hAtomOutside
  have hRestrict : μatom.restrict A = μatom :=
    Measure.restrict_eq_self_of_ae_mem hAE
  have hAtomicSum :
      (∫⁻ s : ℝ, f s ∂μatom) = ∑' a : A, f a.1 * μatom {a.1} := by
    calc
      (∫⁻ s : ℝ, f s ∂μatom) =
          (∫⁻ s : ℝ, f s ∂(μatom.restrict A)) := by rw [hRestrict]
      _ = ∑' a : A, f a.1 * μatom {a.1} :=
        MeasureTheory.lintegral_countable f hCount
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
    _ = (∑' a : A, f a.1 * μatom {a.1}) +
          (∫⁻ s : ℝ, f s ∂μdiffuse) := by rw [hAtomicSum]
