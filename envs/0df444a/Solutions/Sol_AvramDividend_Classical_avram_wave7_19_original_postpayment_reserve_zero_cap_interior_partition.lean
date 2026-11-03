-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_postpayment_reserve_zero_cap_interior_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:42:41.891894+00:00
-- url     : https://prove2.me/submissions/621fea7f-4e8c-45dd-bdaf-e3577034b259

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_within_cap_before_ruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Right-paid reserve at a genuine payment is either on the zero face,
on the cap face, or strictly inside the reserve interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C) (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω)) :
    let y := x + X.X t ω - rightLimit D t ω
    y = 0 ∨ ENNReal.ofReal y = C ∨
      (0 < y ∧ ENNReal.ofReal y < C) := by
  dsimp
  have hlo : 0 ≤ x + X.X t ω - rightLimit D t ω := by
    rcases ht with hzero | ⟨ht0, hbefore⟩
    · subst t
      exact (capped_postPaymentReserve_initial_state X x C D hD hxc ω).1
    · exact (capped_postPaymentReserve_within_cap_before_ruin
        X x C D hD ω t ht0 hbefore).1
  have hhi : ENNReal.ofReal (x + X.X t ω - rightLimit D t ω) ≤ C :=
    capped_postPaymentReserve_ofReal_le_cap X x C D hD hxc ω t
  rcases eq_or_lt_of_le hlo with hzero | hpos
  · left
    exact hzero.symm
  · rcases eq_or_lt_of_le hhi with hcap | hinterior
    · right
      left
      exact hcap
    · right
      right
      exact ⟨hpos, hinterior⟩
