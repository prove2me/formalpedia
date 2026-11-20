-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_stopped_truejump_JL_onecell_source_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:20:32.078528+00:00
-- url     : https://prove2.me/submissions/814a6cdf-7186-40e8-af2a-61948172d35f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_masked_discounted_negative_JL_onecell_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρT : ∀ ω, ρ ω ≤ T)
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (u v δ η : ℝ) (hη : 0 < η) (hηone : η < 1) :
    let a : ℝ≥0 × Ω → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then
          deriv w (Y p.1) else 0) else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    ∀ (t : ℝ≥0) (ω : Ω) (z : ℝ), z < 0 →
      (if t ≤ ρ ω then GW ((t, ω), z) else 0) +
      (if t ≤ ρ ω ∧ z ∈ Ioo (-1 : ℝ) (-η) then
        Real.exp (-(q * (t : ℝ))) *
          (if Y (t, ω) ∈ Icc (u + δ) v then deriv w (Y (t, ω)) * z
            else 0) else 0) =
      (if t ≤ ρ ω then Real.exp (-(q * (t : ℝ))) *
        ((if Y (t, ω) ∈ Icc (u + δ) v then
          w (Y (t, ω) + z) - w (Y (t, ω)) else 0) -
         (if -η ≤ z then
           z * (if Y (t, ω) ∈ Icc (u + δ) v then
             deriv w (Y (t, ω)) else 0) else 0)) else 0) := by
  intro a Y H HS GW t ω z hz
  have hbase :=
    AvramDividend.Classical.avram_pj_workerC_original_masked_discounted_negative_JL_onecell_identity
      η z (Real.exp (-(q * (t : ℝ))))
      (if Y (t, ω) ∈ Icc (u + δ) v then
        w (Y (t, ω) + z) - w (Y (t, ω)) else 0)
      (if Y (t, ω) ∈ Icc (u + δ) v then deriv w (Y (t, ω)) else 0)
      hη hηone hz (t ≤ ρ ω)
  by_cases ht : t ≤ ρ ω
  · have hT : t ≤ T := le_trans ht (hρT ω)
    have hr : (t : ℝ≥0∞) ≤ ruinTime X x D ω :=
      (ENNReal.coe_le_coe.mpr ht).trans (hρruin ω)
    have hband : ∀ f : ℝ → ℝ,
        (if Y (t, ω) ∈ Icc (u + δ) v then f (Y (t, ω)) * z else 0) =
        z * (if Y (t, ω) ∈ Icc (u + δ) v then f (Y (t, ω)) else 0) := by
      intro f
      by_cases hy : Y (t, ω) ∈ Icc (u + δ) v <;>
        simp [hy, mul_comm]
    simpa [a, H, HS, GW, ht, hT, hr, hband, mul_comm,
      mul_left_comm, mul_assoc] using hbase
  · simpa [a, H, HS, GW, ht] using hbase

