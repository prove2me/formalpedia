-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_cell_endpoint_limits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:14:13.662572+00:00
-- url     : https://prove2.me/submissions/c533d09a-1196-4cbd-8171-094ce759a58c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (θ t : ℝ≥0) (ht : 0 < t) (htθ : t ≤ θ)
    (he : (t : ℝ≥0∞) < ruinTime X x D ω)
    (l r : ℕ → ℝ≥0)
    (hl : Tendsto l atTop (𝓝[<] t))
    (hr : Tendsto r atTop (𝓝[Ici t] t)) :
    Tendsto (fun n => x + X.X (r n) ω - rightLimit D (l n) ω)
      atTop (𝓝 (riskProcess X x D t ω)) ∧
    Tendsto (fun n => if r n = θ ∧ ¬ (r n = 0 ∨ (r n : ℝ≥0∞) < ruinTime X x D ω)
      then riskProcess X x D (r n) ω else x + X.X (r n) ω - rightLimit D (r n) ω)
      atTop (𝓝 (x + X.X t ω - rightLimit D t ω)) ∧
    Tendsto (fun n => Real.exp (-(q * (r n : ℝ)))) atTop (𝓝 (Real.exp (-(q * (t : ℝ))))) := by 
  have hXR : Tendsto (fun s : ℝ≥0 => X.X s ω) (𝓝[Ici t] t) (𝓝 (X.X t ω)) :=
    X.rightCont ω t
  have hL := (avram_wave3_04_rightLimit_leftLimit_eq_dividend D hD ω t ht).comp hl
  have hY : Tendsto (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
      (𝓝[Ici t] t) (𝓝 (x + X.X t ω - rightLimit D t ω)) :=
    (postPaymentReserve_cadlag_adapted X x D hD).1 ω t
  have hYlim : Tendsto (fun n => x + X.X (r n) ω - rightLimit D (r n) ω)
      atTop (𝓝 (x + X.X t ω - rightLimit D t ω)) := hY.comp hr
  have hgood : ∀ᶠ n in atTop, ¬ (r n = θ ∧ ¬ (r n = 0 ∨ (r n : ℝ≥0∞) < ruinTime X x D ω)) := by
    by_cases h : t = θ
    · exact Filter.Eventually.of_forall (fun n hn => hn.2 (Or.inr (by rw [hn.1, ← h]; exact he)))
    · have hlt : t < θ := lt_of_le_of_ne htθ h
      have hc : Tendsto (fun _ : ℕ => θ) atTop (𝓝 θ) := tendsto_const_nhds
      filter_upwards [(tendsto_nhdsWithin_iff.mp hr).1.eventually_lt hc hlt] with n hn hb
      exact (ne_of_lt hn) hb.1
  have hdisc : Continuous (fun s : ℝ≥0 => Real.exp (-(q * (s : ℝ)))) := by fun_prop
  refine ⟨?_, hYlim.congr' (hgood.mono (fun n hn => (if_neg hn).symm)), ?_⟩
  · simpa only [riskProcess, Function.comp_apply] using
      ((tendsto_const_nhds.add (hXR.comp hr)).sub hL : Tendsto
        (fun n => x + X.X (r n) ω - rightLimit D (l n) ω) atTop
        (𝓝 (x + X.X t ω - D t ω)))
  · exact hdisc.continuousAt.tendsto.comp (tendsto_nhdsWithin_iff.mp hr).1
