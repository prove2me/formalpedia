-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_real_payment_stieltjes_zero_cap_spatial_eventual_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:57:38.495021+00:00
-- url     : https://prove2.me/submissions/98883fca-f772-4b29-9abe-6854bdbeff14

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
/-- Every genuine real Stieltjes payment is eventually covered by zero/cap plus interior bands. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxc : ENNReal.ofReal x ≤ C) (T : ℝ)
    (lower : ℕ → ℝ) (upper : ℕ → ℝ≥0∞)
    (hlower : Filter.Tendsto lower Filter.atTop (𝓝 0))
    (hupper : Filter.Tendsto upper Filter.atTop (𝓝 C)) :
    ∀ (ω : Ω) (t : ℝ),
      t ∈ paymentTimes (ruinTime X x D ω) ∩ Iic T →
      ∀ᶠ n : ℕ in Filter.atTop,
        x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω = 0 ∨
          ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) = C ∨
            (lower n < x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω ∧
              ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) < upper n) := by
  intro ω t ht
  have hpay : t ∈ paymentTimes (ruinTime X x D ω) := by
    exact ht.1
  change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < ruinTime X x D ω) at hpay
  have hclock : t.toNNReal = 0 ∨
      (0 < t.toNNReal ∧
        ((t.toNNReal : ℝ≥0∞) < ruinTime X x D ω)) := by
    rcases hpay with ⟨htnonneg, hsurvive⟩
    by_cases hzero : t = 0
    · exact Or.inl (by simp [hzero])
    · right
      have hpos : 0 < t := by
        rcases lt_or_eq_of_le htnonneg with hp | heq
        · exact hp
        · exact False.elim (hzero heq.symm)
      have hnnpos : 0 < t.toNNReal := Real.toNNReal_pos.mpr hpos
      rcases hsurvive with hz | hbefore
      · exact (hzero hz).elim
      · change (t.toNNReal : ℝ≥0∞) < ruinTime X x D ω at hbefore
        exact ⟨hnnpos, hbefore⟩
  have hnonneg : 0 ≤ x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω := by
    rcases hclock with hz | ⟨hpos, hbefore⟩
    · simpa [hz] using
        (capped_postPaymentReserve_initial_state X x C D hD hxc ω).1
    · exact (capped_postPaymentReserve_within_cap_before_ruin
        X x C D hD ω t.toNNReal hpos hbefore).1
  have hcap : ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) ≤ C :=
    capped_postPaymentReserve_ofReal_le_cap X x C D hD hxc ω t.toNNReal
  rcases eq_or_lt_of_le hnonneg with hzero | hpos
  · exact Filter.Eventually.of_forall (fun _ => Or.inl hzero.symm)
  · rcases eq_or_lt_of_le hcap with hatcap | hinside
    · exact Filter.Eventually.of_forall (fun _ => Or.inr (Or.inl hatcap))
    · have hlow : ∀ᶠ n : ℕ in Filter.atTop, lower n < x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω :=
        hlower.eventually (Iio_mem_nhds hpos)
      have hupp : ∀ᶠ n : ℕ in Filter.atTop,
          ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) < upper n :=
        hupper.eventually (Ioi_mem_nhds hinside)
      filter_upwards [hlow, hupp] with n hnlo hnup
      exact Or.inr (Or.inr ⟨hnlo, hnup⟩)
