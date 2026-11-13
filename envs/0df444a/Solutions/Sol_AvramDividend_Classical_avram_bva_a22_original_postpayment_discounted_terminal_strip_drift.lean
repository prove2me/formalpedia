-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_postpayment_discounted_terminal_strip_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:22:08.530207+00:00
-- url     : https://prove2.me/submissions/925da515-cd03-4c2b-9e8c-737b96325c86

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_postpayment_compact_terminal_upper_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (c d L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ y ∈ Icc c d, ∀ z ∈ Icc c d,
      w z - w y ≤ L * max (z - y) 0) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      (x + X.X s ω - rightLimit D s ω) ∈ Icc c d →
      (x + X.X t ω - rightLimit D t ω) ∈ Icc c d →
      0 ≤ w (x + X.X t ω - rightLimit D t ω) →
      Real.exp (-(q * (t : ℝ))) *
        w (x + X.X t ω - rightLimit D t ω) -
        Real.exp (-(q * (s : ℝ))) *
        w (x + X.X s ω - rightLimit D s ω) ≤
      L * (((t : ℝ) - (s : ℝ)) * max X.drift 0) := by
  filter_upwards
    [avram_bva_a22_original_postpayment_compact_terminal_upper_drift
      X hBV x D hD w c d L hL hLip] with ω hω
  intro s t hst hs ht hwt
  have hsle : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
  have htime : 0 ≤ (s : ℝ) := s.property
  have hΔ : 0 ≤ (t : ℝ) - (s : ℝ) := sub_nonneg.mpr hsle
  have hqt : q * (s : ℝ) ≤ q * (t : ℝ) :=
    mul_le_mul_of_nonneg_left hsle hq
  have hdisc :
      Real.exp (-(q * (t : ℝ))) ≤ Real.exp (-(q * (s : ℝ))) :=
    Real.exp_le_exp.mpr (neg_le_neg hqt)
  have hdisc0 : 0 ≤ Real.exp (-(q * (s : ℝ))) := (Real.exp_pos _).le
  have hdisc1 : Real.exp (-(q * (s : ℝ))) ≤ 1 := by
    calc
      Real.exp (-(q * (s : ℝ))) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg hq htime))
      _ = 1 := Real.exp_zero
  have hB : 0 ≤ L * (((t : ℝ) - (s : ℝ)) * max X.drift 0) :=
    mul_nonneg hL (mul_nonneg hΔ (le_max_right _ _))
  have hUp := hω s t hst hs ht
  have hScaled :
      Real.exp (-(q * (s : ℝ))) *
        (w (x + X.X t ω - rightLimit D t ω) -
          w (x + X.X s ω - rightLimit D s ω)) ≤
        Real.exp (-(q * (s : ℝ))) *
          (L * (((t : ℝ) - (s : ℝ)) * max X.drift 0)) :=
    mul_le_mul_of_nonneg_left hUp hdisc0
  calc
    Real.exp (-(q * (t : ℝ))) *
        w (x + X.X t ω - rightLimit D t ω) -
        Real.exp (-(q * (s : ℝ))) *
        w (x + X.X s ω - rightLimit D s ω) ≤
      Real.exp (-(q * (s : ℝ))) *
        w (x + X.X t ω - rightLimit D t ω) -
        Real.exp (-(q * (s : ℝ))) *
        w (x + X.X s ω - rightLimit D s ω) := by
          exact sub_le_sub_right (mul_le_mul_of_nonneg_right hdisc hwt) _
    _ = Real.exp (-(q * (s : ℝ))) *
        (w (x + X.X t ω - rightLimit D t ω) -
          w (x + X.X s ω - rightLimit D s ω)) := by ring
    _ ≤ Real.exp (-(q * (s : ℝ))) *
        (L * (((t : ℝ) - (s : ℝ)) * max X.drift 0)) := hScaled
    _ ≤ 1 * (L * (((t : ℝ) - (s : ℝ)) * max X.drift 0)) :=
      mul_le_mul_of_nonneg_right hdisc1 hB
    _ = L * (((t : ℝ) - (s : ℝ)) * max X.drift 0) := one_mul _
