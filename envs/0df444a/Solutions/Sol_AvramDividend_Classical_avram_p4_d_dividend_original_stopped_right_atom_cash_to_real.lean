-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_stopped_right_atom_cash_to_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:51:28.052387+00:00
-- url     : https://prove2.me/submissions/37671a9e-fa67-474a-970d-9ab633c18192

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The original closed Stieltjes singleton's discounted toReal cash is
exactly the post-right-payment physical mass at each eligible event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T t : ℝ≥0) (ht : t ≤ T)
    (hδ : 0 ≤ rightLimit D t ω - D t ω) (q : ℝ) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    (μ {(t : ℝ)} *
      (if (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)
        then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
        else 0)).toReal =
      if (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)
        then (rightLimit D t ω - D t ω) * Real.exp (-(q * (t : ℝ)))
        else 0 := by
  let μ : Measure ℝ :=
    (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  change (μ {(t : ℝ)} *
    (if (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)
      then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
      else 0)).toReal =
    if (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)
      then (rightLimit D t ω - D t ω) * Real.exp (-(q * (t : ℝ)))
      else 0
  obtain ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit,
      hAtoms, hAtomCompl, hNull, hSingleton, hMass⟩ :=
    avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse
      D hD ω T
  have hAtom : μ {(t : ℝ)} =
      ENNReal.ofReal (rightLimit D t ω - D t ω) := hSingleton t ht
  have he : 0 ≤ Real.exp (-(q * (t : ℝ))) :=
    (Real.exp_pos _).le
  by_cases hp : (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)
  · simp only [if_pos hp]
    rw [hAtom, ← ENNReal.ofReal_mul hδ]
    exact ENNReal.toReal_ofReal (mul_nonneg hδ he)
  · simp only [if_neg hp, mul_zero, ENNReal.toReal_zero]