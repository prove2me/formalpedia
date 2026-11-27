-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_left_limit_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:55:50.184729+00:00
-- url     : https://prove2.me/submissions/b716992f-bcd4-4584-9393-341d487faeb0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (δ R : ℝ) (θ : Ω → ℝ≥0)
    (hprefix : ∀ ω t, t < θ ω →
      x + X.X t ω - rightLimit D t ω ∈ Icc δ R) :
    ∀ ω (t : ℝ≥0), 0 < t → t ≤ θ ω →
      let y := Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
      y ∈ Icc δ R ∧ ENNReal.ofReal y ≤ C := by 
  intro ω t ht hle
  let Y : ℝ≥0 → ℝ := fun s => x + X.X s ω - rightLimit D s ω
  obtain ⟨l, hl⟩ := (postPaymentReserve_cadlag_adapted X x D hD.1.1).2.1 ω t ht
  letI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have he : Function.leftLim Y t = l := leftLim_eq_of_tendsto hl
  have hb : ∀ᶠ s : ℝ≥0 in 𝓝[<] t, Y s ∈ Icc δ R := by
    filter_upwards [Ioo_mem_nhdsLT ht] with s hs
    exact hprefix ω s (hs.2.trans_le hle)
  have hc : ∀ᶠ s : ℝ≥0 in 𝓝[<] t, ENNReal.ofReal (Y s) ≤ C := by
    filter_upwards [Ioo_mem_nhdsLT ht] with s hs
    have hd := dividendStrategy_le_rightLimit D hD.1.1 ω s
    have hY : Y s ≤ riskProcess X x D s ω := by
      change x + X.X s ω - rightLimit D s ω ≤ x + X.X s ω - D s ω
      linarith
    exact (ENNReal.ofReal_le_ofReal hY).trans (hD.2 ω s hs.1)
  change Function.leftLim Y t ∈ Icc δ R ∧ ENNReal.ofReal (Function.leftLim Y t) ≤ C
  rw [he]
  exact ⟨isClosed_Icc.mem_of_tendsto hl hb,
    isClosed_Iic.mem_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hl) hc⟩
