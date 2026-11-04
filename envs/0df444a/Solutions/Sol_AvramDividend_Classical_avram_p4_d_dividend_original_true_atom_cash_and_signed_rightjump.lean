-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_true_atom_cash_and_signed_rightjump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:56:28.318868+00:00
-- url     : https://prove2.me/submissions/9745d2a3-6e5d-4ed8-978a-4d65fc72a7e0

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Exact original true-payment atomic cash and nonpositive simultaneous
source-first, dividend-second Itô right-jump correction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤
        w (riskProcess X x D s ω) -
          w (riskProcess X x D s ω -
            (rightLimit D s ω - D s ω)))
    (ω : Ω) (T t : ℝ≥0) (ht : t ≤ T)
    (hPre : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ((μ {(t : ℝ)} *
      (if (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)
        then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
        else 0)).toReal =
      if (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)
        then (rightLimit D t ω - D t ω) * Real.exp (-(q * (t : ℝ)))
        else 0) ∧
    Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) +
        w (x + X.X t ω - rightLimit D t ω) -
        w (riskProcess X x D t ω)) ≤ 0 := by
  let μ : Measure ℝ :=
    (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  change ((μ {(t : ℝ)} *
      (if (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)
        then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
        else 0)).toReal =
      if (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)
        then (rightLimit D t ω - D t ω) * Real.exp (-(q * (t : ℝ)))
        else 0) ∧
    Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) +
        w (x + X.X t ω - rightLimit D t ω) -
        w (riskProcess X x D t ω)) ≤ 0
  constructor
  · obtain ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit,
      hAtoms, hAtomCompl, hNull, hSingleton, hMass⟩ :=
      avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse D hD ω T
    have hAtom : μ {(t : ℝ)} =
        ENNReal.ofReal (rightLimit D t ω - D t ω) :=
      hSingleton t ht
    have hδ : 0 ≤ rightLimit D t ω - D t ω :=
      sub_nonneg.mpr (dividendStrategy_le_rightLimit D hD ω t)
    have he : 0 ≤ Real.exp (-(q * (t : ℝ))) :=
      (Real.exp_pos _).le
    by_cases hp : (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)
    · simp only [if_pos hp]
      rw [hAtom, ← ENNReal.ofReal_mul hδ]
      exact ENNReal.toReal_ofReal (mul_nonneg hδ he)
    · simp only [if_neg hp, mul_zero, ENNReal.toReal_zero]
  · exact avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
      X x D w q hjump (fun _ => t) ω hPre