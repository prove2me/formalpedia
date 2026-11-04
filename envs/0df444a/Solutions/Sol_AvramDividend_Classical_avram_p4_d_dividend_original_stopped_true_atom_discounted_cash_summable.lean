-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_stopped_true_atom_discounted_cash_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:51:00.834732+00:00
-- url     : https://prove2.me/submissions/1cf625c2-cbcd-42f4-abde-c83688e0d8d6

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

/-- The authentic original stopped Stieltjes atom cash has finite real
series mass, with time zero and the payment/ruin endpoint selector intact. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ A : Set ℝ,
      A.Countable ∧
      (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) ∧
      Summable (fun t : A =>
        (μ {(t : ℝ)} *
          (if (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)
            then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
            else 0)).toReal) := by
  let μ : Measure ℝ :=
    (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  change ∃ A : Set ℝ,
    A.Countable ∧
    (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) ∧
    Summable (fun t : A =>
      (μ {(t : ℝ)} *
        (if (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)
          then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
          else 0)).toReal)
  obtain ⟨A, ν, hCount, _hMeas, _hNull, _hAtom, hSupport, hSplit, hBound⟩ :=
    avram_wave6_05_actual_original_stopped_discounted_all_atoms_diffuse_cash_bound
      X x q hq D hD ω T
  have hAtomLe :
      (∑' t : A, μ {(t : ℝ)} *
        (if (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)
          then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
          else 0)) ≤ ENNReal.ofReal (rightLimit D T ω) := by
    calc
      _ ≤ (∑' t : A, μ {(t : ℝ)} *
        (if (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)
          then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
          else 0)) +
          (∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω)
            then ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂ν) :=
        le_add_of_nonneg_right zero_le
      _ = (∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω)
          then ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μ) :=
        hSplit.symm
      _ ≤ ENNReal.ofReal (rightLimit D T ω) := hBound
  refine ⟨A, hCount, hSupport, ?_⟩
  exact ENNReal.summable_toReal
    (ne_of_lt (lt_of_le_of_lt hAtomLe ENNReal.ofReal_lt_top))