-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_cash_coverage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:15:59.221282+00:00
-- url     : https://prove2.me/submissions/8ff6a4d3-6fac-43bd-9b72-4450e05ffadd

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gclose15_original_compact_strict_postpayment_uniform_floor
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_bounded_compact_horizon
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ) (hT : 0 ≤ T) (δ R : ℕ → ℝ)
    (hd : Tendsto δ atTop (𝓝 0)) (hR : Tendsto R atTop atTop)
    (θ : ℕ → Ω → ℝ≥0)
    (hcover : ∀ k ω t, t ≤ T.toNNReal →
      (∀ s : ℝ≥0, s ≤ t → x + X.X s ω - rightLimit D s ω ∈ Icc (δ k) (R k)) →
      t ≤ θ k ω)
    (hpos : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T.toNNReal →
      (t : ℝ≥0∞) < ruinTime X x D ω → 0 < x + X.X t ω - rightLimit D t ω) :
    ∀ᵐ ω ∂P, ∀ t ∈ paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ∃ k, t ≤ (θ k ω : ℝ) := by 
  filter_upwards [hpos] with ω hω
  intro t ht
  have ht0 : 0 ≤ t := ht.1.1
  by_cases hzero : t = 0
  · subst t
    exact ⟨0, by positivity⟩
  have hruin : ENNReal.ofReal t < ruinTime X x D ω :=
    ht.1.2.resolve_left hzero
  let u : ℝ≥0 := t.toNNReal
  have hu : (u : ℝ) = t := Real.coe_toNNReal t ht0
  have huH : u ≤ T.toNNReal := Real.toNNReal_le_toNNReal ht.2
  have huR : (u : ℝ≥0∞) < ruinTime X x D ω := by
    rw [← hu] at hruin
    simpa only [ENNReal.ofReal_coe_nnreal] using hruin
  obtain ⟨a, ha, haBound⟩ :=
    avram_gclose15_original_compact_strict_postpayment_uniform_floor X x D hD ω u
      (fun s hs => hω s (hs.trans huH) (lt_of_le_of_lt (by exact_mod_cast hs) huR))
  obtain ⟨b, hb⟩ := (postPaymentReserve_bounded_compact_horizon X x D hD ω u).bddAbove
  have hev : ∀ᶠ k in atTop, δ k < a ∧ b ≤ R k :=
    (hd.eventually (Iio_mem_nhds ha)).and (hR.eventually (eventually_ge_atTop b))
  obtain ⟨k, hk⟩ := hev.exists
  refine ⟨k, ?_⟩
  have hle := hcover k ω u huH (fun s hs =>
    ⟨hk.1.le.trans (haBound s hs), (hb ⟨s, ⟨zero_le, hs⟩, rfl⟩).trans hk.2⟩)
  rw [← hu]
  exact_mod_cast hle
