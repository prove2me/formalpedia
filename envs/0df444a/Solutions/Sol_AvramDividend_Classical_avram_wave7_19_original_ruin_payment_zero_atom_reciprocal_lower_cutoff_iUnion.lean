-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_ruin_payment_zero_atom_reciprocal_lower_cutoff_iUnion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:08:45.303907+00:00
-- url     : https://prove2.me/submissions/ddd9a214-b5a3-4828-a474-0d22ae57723c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Positive lower-time cutoffs omit the right-payment at time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T : ℝ) (hT : 0 ≤ T) :
    paymentTimes (ruinTime X x D ω) ∩ Iic T =
      ({0} : Set ℝ) ∪
        ⋃ n : ℕ, paymentTimes (ruinTime X x D ω) ∩
          Icc (1 / ((n : ℝ) + 1)) T := by
  classical
  ext t
  constructor
  · rintro ⟨htPay, htT⟩
    by_cases htzero : t = 0
    · exact Or.inl (by simpa [htzero])
    · have htpos : 0 < t := by
        exact lt_of_le_of_ne htPay.1 (Ne.symm htzero)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt htpos
      refine Or.inr (Set.mem_iUnion.mpr ⟨n, ?_⟩)
      exact ⟨htPay, ⟨le_of_lt hn, htT⟩⟩
  · intro h
    rcases h with hzero | hrest
    · have htzero : t = 0 := by simpa using hzero
      subst t
      exact ⟨⟨le_rfl, Or.inl rfl⟩, hT⟩
    · obtain ⟨n, ⟨htPay, htBand⟩⟩ := Set.mem_iUnion.mp hrest
      exact ⟨htPay, htBand.2⟩
