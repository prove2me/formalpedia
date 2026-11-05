-- Prove2me | solution 2 for AvramDividend.Classical.avram_p3_bv_original_cash_strict_left_union
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:49:14.956908+00:00
-- url     : https://prove2.me/submissions/be0fa5a5-b6bf-48c3-9aef-e73ac0ee6e78

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The original payment set strictly before the horizon is exactly the union
of payment sets before any cofinal family of earlier real cutoffs. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T : ℝ) (u : ℕ → ℝ)
    (hbelow : ∀ n, u n ≤ T)
    (hcover : ∀ s : ℝ, s < T → ∃ n, s < u n) :
    (⋃ n, paymentTimes (ruinTime X x D ω) ∩ Iio (u n)) =
      paymentTimes (ruinTime X x D ω) ∩ Iio T := by
  ext s
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Iio]
  constructor
  · rintro ⟨n, hp, hlt⟩
    exact ⟨hp, lt_of_lt_of_le hlt (hbelow n)⟩
  · rintro ⟨hp, hlt⟩
    obtain ⟨n, hn⟩ := hcover s hlt
    exact ⟨n, hp, hn⟩
