-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_discounted_real_atomic_diffuse_cash_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:39:05.23034+00:00
-- url     : https://prove2.me/submissions/1fce665b-e4cf-4a61-8e4c-12553968d2d8

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_discounted_closed_atomic_diffuse_cash_split
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_stopped_payment_discounted_le_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The original closed discounted atom/diffuse Cash split remains exact in real L¹ units. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (ω : Ω) (T : ℝ≥0) :
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
      ((∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal =
          (∫⁻ s : ℝ, f s ∂μatom).toReal +
          (∫⁻ s : ℝ, f s ∂μdiffuse).toReal) := by
  obtain ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit,
      hNull, hAtomOutside, hDiffCarrier, hSingleton, hMass, hCash⟩ :=
    avram_p4_d_dividend_original_discounted_closed_atomic_diffuse_cash_split
      X x D hD q ω T
  refine ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit,
    hNull, hAtomOutside, hDiffCarrier, hSingleton, hMass, ?_⟩
  let f : ℝ → ℝ≥0∞ := fun s =>
    if s ∈ paymentTimes (ruinTime X x D ω)
    then ENNReal.ofReal (Real.exp (-(q * s))) else 0
  let a : ℝ≥0∞ := ∫⁻ s : ℝ, f s ∂μatom
  let b : ℝ≥0∞ := ∫⁻ s : ℝ, f s ∂μdiffuse
  let z : ℝ≥0∞ := ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
    ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)
  have hBound : z ≤ ENNReal.ofReal (rightLimit D T ω) :=
    avram_wave3_03_bv_stopped_payment_discounted_le_rightLimit
      q hq D hD ω (ruinTime X x D ω) T
  have hzFinite : z ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hBound ENNReal.ofReal_lt_top)
  have haFinite : a ≠ ⊤ := by
    intro ha
    apply hzFinite
    calc
      z = a + b := hCash
      _ = ⊤ := by simp [ha]
  have hbFinite : b ≠ ⊤ := by
    intro hb
    apply hzFinite
    calc
      z = a + b := hCash
      _ = ⊤ := by simp [hb]
  calc
    z.toReal = (a + b).toReal := congrArg ENNReal.toReal hCash
    _ = a.toReal + b.toReal := ENNReal.toReal_add haFinite hbFinite
