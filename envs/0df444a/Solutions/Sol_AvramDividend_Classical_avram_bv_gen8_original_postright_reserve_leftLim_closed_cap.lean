-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:51:05.209099+00:00
-- url     : https://prove2.me/submissions/7e7b8b9a-05e7-49c8-b610-6f32faee2c8f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_postrightpayment_reserve_closed_cap
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_leftLim_origin_nnreal
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The source post-right-payment reserve remains capped at its genuine
strict-left state at every active time, including the time-zero atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (hactive : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    let Z : ℝ := Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    0 ≤ Z ∧ ENNReal.ofReal Z ≤ C := by
  dsimp
  by_cases hzero : t = 0
  · subst t
    simpa only [avram_p2_a_zero_rate_leftLim_origin_nnreal] using
      (avram_p4_d_dividend_postrightpayment_reserve_closed_cap
        X x C hxc D hD ω 0 (Or.inl rfl))
  · have hstop : (t : ℝ≥0∞) < ruinTime X x D ω :=
      hactive.resolve_left hzero
    have ht : (0 : ℝ≥0) < t :=
      lt_of_le_of_ne (show (0 : ℝ≥0) ≤ t from bot_le) (Ne.symm hzero)
    letI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
    obtain ⟨u, hu⟩ := X.leftLim ω t ht
    have hDleft :=
      avram_wave3_04_rightLimit_leftLimit_eq_dividend D hD.1.1 ω t ht
    have hU : Tendsto
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
        (𝓝[<] t) (𝓝 (x + u - D t ω)) := by
      convert (tendsto_const_nhds.add hu).sub hDleft using 1
    have hUlim : Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t =
        x + u - D t ω := leftLim_eq_of_tendsto hU
    have hclosed : IsClosed
        {r : ℝ | 0 ≤ r ∧ ENNReal.ofReal r ≤ C} := by
      have hc : IsClosed
          (Ici (0 : ℝ) ∩ (ENNReal.ofReal ⁻¹' Iic C)) :=
        isClosed_Ici.inter (isClosed_Iic.preimage ENNReal.continuous_ofReal)
      convert hc using 1
      ext r
      simp
    have hevent : ∀ᶠ s : ℝ≥0 in 𝓝[<] t,
        0 ≤ x + X.X s ω - rightLimit D s ω ∧
        ENNReal.ofReal (x + X.X s ω - rightLimit D s ω) ≤ C := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hstle : (s : ℝ≥0∞) ≤ (t : ℝ≥0∞) := by
        exact_mod_cast (le_of_lt hs)
      exact avram_p4_d_dividend_postrightpayment_reserve_closed_cap
        X x C hxc D hD ω s (Or.inr (lt_of_le_of_lt hstle hstop))
    have hval := hclosed.mem_of_tendsto hU hevent
    change 0 ≤ x + u - D t ω ∧
      ENNReal.ofReal (x + u - D t ω) ≤ C at hval
    simpa only [hUlim] using hval

