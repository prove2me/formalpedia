-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_zero_cap_preserved_shrinking_spatial_windows_eventual_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:44:27.076104+00:00
-- url     : https://prove2.me/submissions/1d822a66-aa3b-4ee7-9d74-57b113277767

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_within_cap_before_ruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
/-- Original cap and zero boundary payments remain covered as both interior cutoffs vanish. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C)
    (lower : ℕ → ℝ) (upper : ℕ → ℝ≥0∞)
    (hlower : Filter.Tendsto lower Filter.atTop (𝓝 0))
    (hupper : Filter.Tendsto upper Filter.atTop (𝓝 C))
    (hlower_pos : ∀ n, 0 < lower n)
    (hupper_cap : ∀ n, upper n < C) :
    (∀ n y, lower n < y ∧ ENNReal.ofReal y < upper n →
      0 < y ∧ ENNReal.ofReal y < C) ∧
    (∀ (ω : Ω) (t : ℝ≥0),
      t = 0 ∨ (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω) →
      ∀ᶠ n : ℕ in Filter.atTop,
        x + X.X t ω - rightLimit D t ω = 0 ∨
          ENNReal.ofReal (x + X.X t ω - rightLimit D t ω) = C ∨
            (lower n < x + X.X t ω - rightLimit D t ω ∧
              ENNReal.ofReal (x + X.X t ω - rightLimit D t ω) < upper n)) := by
  constructor
  · intro n y hy
    constructor
    · exact lt_trans (hlower_pos n) hy.1
    · exact lt_trans hy.2 (hupper_cap n)
  · intro ω t ht
    have hnonneg : 0 ≤ x + X.X t ω - rightLimit D t ω := by
      rcases ht with hzero | ⟨ht0, hbefore⟩
      · subst t
        exact (capped_postPaymentReserve_initial_state X x C D hD hxc ω).1
      · exact (capped_postPaymentReserve_within_cap_before_ruin
          X x C D hD ω t ht0 hbefore).1
    have hcap : ENNReal.ofReal (x + X.X t ω - rightLimit D t ω) ≤ C :=
      capped_postPaymentReserve_ofReal_le_cap X x C D hD hxc ω t
    rcases eq_or_lt_of_le hnonneg with hzero | hpos
    · exact Filter.Eventually.of_forall (fun _ => Or.inl hzero.symm)
    · rcases eq_or_lt_of_le hcap with hatcap | hinside
      · exact Filter.Eventually.of_forall (fun _ => Or.inr (Or.inl hatcap))
      · have hlow : ∀ᶠ n : ℕ in Filter.atTop, lower n < x + X.X t ω - rightLimit D t ω :=
          hlower.eventually (Iio_mem_nhds hpos)
        have hupp : ∀ᶠ n : ℕ in Filter.atTop,
            ENNReal.ofReal (x + X.X t ω - rightLimit D t ω) < upper n :=
          hupper.eventually (Ioi_mem_nhds hinside)
        filter_upwards [hlow, hupp] with n hln hun
        exact Or.inr (Or.inr ⟨hln, hun⟩)
