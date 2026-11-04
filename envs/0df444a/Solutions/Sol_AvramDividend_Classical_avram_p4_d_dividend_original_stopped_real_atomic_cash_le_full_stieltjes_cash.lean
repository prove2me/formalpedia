-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_stopped_real_atomic_cash_le_full_stieltjes_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:38:39.852627+00:00
-- url     : https://prove2.me/submissions/a4902c4e-ac56-4e8a-8450-134e381419f7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_stopped_discounted_all_atoms_diffuse_cash_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Exact original stopped real atomic dividend cash is bounded by all
literal Stieltjes cash, including the singular-continuous remainder. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ A : Set ℝ, A.Countable ∧
      (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) ∧
      (∑' t : A, (μ {(t : ℝ)} *
        (if (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)
          then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
          else 0)).toReal) ≤
        (∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω)
          then ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μ).toReal := by
  let μ : Measure ℝ :=
    (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  change ∃ A : Set ℝ, A.Countable ∧
    (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) ∧
    (∑' t : A, (μ {(t : ℝ)} *
      (if (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)
        then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
        else 0)).toReal) ≤
      (∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω)
        then ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μ).toReal
  obtain ⟨A, ν, hCount, _hMeas, _hNull, _hSingleton,
      hSupport, hSplit, hBound⟩ :=
    avram_wave6_05_actual_original_stopped_discounted_all_atoms_diffuse_cash_bound
      X x q hq D hD ω T
  let f : A → ℝ≥0∞ := fun t =>
    μ {(t : ℝ)} *
      (if (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)
        then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
        else 0)
  have hSplitF : (∫⁻ s : ℝ,
      (if s ∈ paymentTimes (ruinTime X x D ω)
        then ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μ) =
        (∑' t : A, f t) +
        (∫⁻ s : ℝ,
          (if s ∈ paymentTimes (ruinTime X x D ω)
            then ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂ν) := hSplit
  have hAtomLe : (∑' t : A, f t) ≤
      (∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω)
        then ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μ) := by
    rw [hSplitF]
    exact le_add_of_nonneg_right zero_le
  have hTotalFinite : (∫⁻ s : ℝ,
      (if s ∈ paymentTimes (ruinTime X x D ω)
        then ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μ) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hBound ENNReal.ofReal_lt_top)
  have hAtomFinite : (∑' t : A, f t) < ⊤ :=
    lt_of_le_of_lt hAtomLe (lt_of_le_of_lt hBound ENNReal.ofReal_lt_top)
  have hTermFinite (t : A) : f t ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (ENNReal.le_tsum t) hAtomFinite)
  refine ⟨A, hCount, hSupport, ?_⟩
  calc
    (∑' t : A, (f t).toReal) = (∑' t : A, f t).toReal :=
      (ENNReal.tsum_toReal_eq hTermFinite).symm
    _ ≤ (∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω)
        then ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μ).toReal :=
      ENNReal.toReal_mono hTotalFinite hAtomLe

