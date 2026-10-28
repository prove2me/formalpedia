-- Prove2me | solution 1 for AvramDividend.Classical.killed_nextRecord_discount_global_shifted_twoSided_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:20:47.620375+00:00
-- url     : https://prove2.me/submissions/ffda529d-15c6-4df0-ab83-bee393605699

import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_killed_nextRecord_discount_le_shifted_twoSided_of_finite_records
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-! Reduce the unrestricted first-record estimate to the verified finite-clock theorem on the successful event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b ε q : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (ρ σ : ℝ≥0∞)
    (hρ : ρ = (⨅ (t : ℝ≥0)
      (_ : ε < X.X ((twoSidedExitUpTime X b ω).toNNReal + t) ω -
          X.X (twoSidedExitUpTime X b ω).toNNReal ω), (t : ℝ≥0∞)))
    (hσ : σ = (⨅ (t : ℝ≥0)
      (_ : X.X ((twoSidedExitUpTime X b ω).toNNReal + t) ω -
          X.X (twoSidedExitUpTime X b ω).toNNReal ω < -a), (t : ℝ≥0∞))) :
    (if twoSidedExitUpTime X (b + ε) ω < barrierRuinTime X a ω then
      ENNReal.ofReal ε *
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X (b + ε) ω).toReal)))
      else 0) ≤
    ENNReal.ofReal ε *
      (ENNReal.ofReal (Real.exp (-(q *
        ((twoSidedExitUpTime X b ω).toNNReal : ℝ)))) *
        (if ρ < σ then
          ENNReal.ofReal (Real.exp (-(q * ρ.toReal)))
        else 0)) := by
  let U := twoSidedExitUpTime X b ω
  let V := twoSidedExitUpTime X (b + ε) ω
  by_cases hs : V < barrierRuinTime X a ω
  · have hbε : b ≤ b + ε := le_add_of_nonneg_right hε
    have hUV : U ≤ V := twoSidedExitUpTime_mono_threshold X b (b + ε) hbε ω
    have hVfin : V < ⊤ := lt_of_lt_of_le hs le_top
    have hUfin : U < ⊤ := lt_of_le_of_lt hUV hVfin
    have hu : ((U.toNNReal : ℝ≥0) : ℝ≥0∞) = U :=
      ENNReal.coe_toNNReal (ne_of_lt hUfin)
    have hv : ((V.toNNReal : ℝ≥0) : ℝ≥0∞) = V :=
      ENNReal.coe_toNNReal (ne_of_lt hVfin)
    have huv : U.toNNReal ≤ V.toNNReal := by
      apply (ENNReal.coe_le_coe).mp
      simpa only [hu, hv] using hUV
    have hdelta : U.toNNReal + (V.toNNReal - U.toNNReal) = V.toNNReal :=
      add_tsub_cancel_of_le huv
    have hAt : X.X U.toNNReal ω = b :=
      (firstUpcrossing_attains_peak X b hb ω U.toNNReal hu).1
    have hEstimate :=
      killed_nextRecord_discount_le_shifted_twoSided_of_finite_records
        X ω a b ε q ha hb hε
        U.toNNReal V.toNNReal (V.toNNReal - U.toNNReal)
        hu hAt hv hdelta ρ σ hρ hσ
    simpa only [U, V] using hEstimate
  · simpa only [U, V, if_neg hs, zero_le]
