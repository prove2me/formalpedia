-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_spatial_fullmark_centered_stopped_reward
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:01:47.689205+00:00
-- url     : https://prove2.me/submissions/cc519792-4902-42a5-be80-c1dae803efb7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_fullmark_initial_event_stopped_reward_sources_exist
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- The original bounded spatial stop retains the physical fullmark source and exact cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (q x : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (hn : 0 < n) (ρ : Ω → ℝ≥0)
    (κ : ℕ → Ω → ℝ≥0)
    (hκexact : ∀ i ω, κ i ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((i : ℝ) + 1) ω)).toNNReal)
    (hκstop : ∀ i, IsStoppingTime 𝓕.rightCont
      (fun ω => (κ i ω : WithTop ℝ≥0)))
    (hκbound : ∀ i ω, κ i ω ≤ (n : ℝ≥0))
    (H : ℕ → Ω → ℝ)
    (hHsource : ∀ i ω, H i ω =
      Real.exp (-(q * (κ i ω : ℝ))) *
        w (if κ i ω = 0 ∨ (κ i ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (κ i ω) ω - rightLimit D (κ i ω) ω
          else riskProcess X x D (κ i ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ i ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ i : ℕ, let μ : ℝ := ∫ ω, X.X 1 ω ∂P
    ∃ (R Jsmall Jfull : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (nhds (R t ω))) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (nhds (Jsmall t ω))) ∧
      (∀ t : ℝ≥0, Integrable (R t) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (R t) ω = R s ω) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Jfull t ω =
          Jsmall t ω + avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
          (t : ℝ) * (X.c - μ)) ∧
      Integrable (fun ω => Jfull (κ i ω) ω) P ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P
        (fun ω => Jfull (κ i ω) ω) ω = 0) ∧
      (∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
        (∫ ω in A, Jfull (κ i ω) ω ∂P) = 0) ∧
      (∀ᵐ ω ∂P, H i ω =
        Real.exp (-(q * (κ i ω : ℝ))) *
          w (x + (κ i ω : ℝ) * μ + R (κ i ω) ω + Jfull (κ i ω) ω -
            (if κ i ω = 0 ∨ (κ i ω : ℝ≥0∞) < ruinTime X x D ω
             then rightLimit D (κ i ω) ω else D (κ i ω) ω)) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ i ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) := by
  intro i
  exact avram_ja18_original_fullmark_initial_event_stopped_reward_sources_exist
    X hX hFinite q x w D n hn (κ i) (hκstop i) (hκbound i)
    (H i) (hHsource i)
