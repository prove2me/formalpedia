-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_clipped_clock_zero_atom_lower_cutoff_lintegral_iSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:15:45.715551+00:00
-- url     : https://prove2.me/submissions/62b99276-0e01-4619-b646-f1f8a1efb057

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_finite_horizon_clock_strict_stabilises
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ruin_cash_zero_atom_lower_cutoff_lintegral_iSup
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ) (hT : 0 ≤ T)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (n : ℕ) (hn : ENNReal.ofReal T < (n : ℝ≥0∞)) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in ({0} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      ⨆ k : ℕ, (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩
        Icc (1 / ((k : ℝ) + 1)) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  classical
  have hclock :=
    avram_wave7_19_original_finite_horizon_clock_strict_stabilises
      X x D ω T hT n hn
  have hset (k : ℕ) :
      paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩
        Icc (1 / ((k : ℝ) + 1)) T =
      paymentTimes (ruinTime X x D ω) ∩ Icc (1 / ((k : ℝ) + 1)) T := by
    ext t
    constructor
    · intro ht
      have hclose :
          t ∈ paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T :=
        ⟨ht.1, ht.2.2⟩
      rw [hclock] at hclose
      exact ⟨hclose.1, ht.2⟩
    · intro ht
      have hclose : t ∈ paymentTimes (ruinTime X x D ω) ∩ Iic T :=
        ⟨ht.1, ht.2.2⟩
      rw [← hclock] at hclose
      exact ⟨hclose.1, ht.2⟩
  rw [avram_wave7_19_original_ruin_cash_zero_atom_lower_cutoff_lintegral_iSup
    X q x T hT D ω]
  congr 1
  apply iSup_congr
  intro k
  rw [hset k]
