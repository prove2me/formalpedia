-- Prove2me | solution 1 for AvramDividend.Classical.avram_gclose15_original_negative_postpayment_usc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T17:56:35.690045+00:00
-- url     : https://prove2.me/submissions/3ce92191-9060-4244-ad13-cb878585210c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_no_positive_jumps
import Theorems.Thm_AvramDividend_Classical_cadlag_no_downward_jumps_upperSemicontinuousOn_Icc

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The negative original postpayment reserve is upper semicontinuous on
every compact time prefix, using the cadlag and downward-jump laws. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    UpperSemicontinuousOn
      (fun t : ℝ≥0 => -(x + X.X t ω - rightLimit D t ω))
      (Icc 0 T) := by
  let R : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
  have hcad := postPaymentReserve_cadlag_adapted X x D hD
  have hdown := avram_wave3_04_postPaymentReserve_no_positive_jumps
    X x D hD ω
  change UpperSemicontinuousOn (fun t => -R t) (Icc 0 T)
  apply cadlag_no_downward_jumps_upperSemicontinuousOn_Icc
  · intro t
    have hfun : (fun s : ℝ≥0 => -R s) = -(fun s : ℝ≥0 => R s) := by
      funext s
      rfl
    rw [hfun]
    exact (hcad.1 ω t).neg
  · intro t ht
    obtain ⟨l, hl, _⟩ := hdown t ht
    refine ⟨-l, ?_⟩
    simpa only [R] using hl.neg
  · intro t l ht hl
    obtain ⟨k, hk, hkle⟩ := hdown t ht
    have hlR : Tendsto R (𝓝[<] t) (𝓝 (-l)) := by
      simpa only [R, neg_neg] using hl.neg
    haveI : (𝓝[<] t).NeBot :=
      nhdsWithin_Iio_self_neBot' ⟨(0 : ℝ≥0), ht⟩
    have hEq : k = -l := tendsto_nhds_unique hk hlR
    change l ≤ -R t
    rw [hEq] at hkle
    dsimp [R] at hkle ⊢
    linarith
