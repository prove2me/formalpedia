-- Prove2me | solution 1 for AvramDividend.Classical.avram_b82_original_jumpfree_limit_small_compensation_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:12:03.860048+00:00
-- url     : https://prove2.me/submissions/bbe5e746-f38c-4db2-93d3-72e28aaba6f8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b80_original_jumpfree_cell_smallband_compensator_increment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original finite-activity intrinsic small-mark process has exactly its limiting deterministic compensator drift on a jumpfree interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJlim : ∀ ω u, Tendsto
      (fun n => avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω)
      atTop (𝓝 (Jsmall u ω)))
    (d : ℝ)
    (hνlim : Tendsto (fun n : ℕ =>
      -(∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν))
      atTop (𝓝 d))
    (s t : Ω → ℝ≥0)
    (hOrder : ∀ ω, s ω ≤ t ω)
    (hNoJump : ∀ ω (u : ℝ≥0), s ω < u → u ≤ t ω →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    ∀ ω, Jsmall (t ω) ω - Jsmall (s ω) ω =
      d * ((t ω : ℝ) - (s ω : ℝ)) := by
  intro ω
  have hCut (n : ℕ) :
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n (t ω) ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n (s ω) ω =
      ((t ω : ℝ) - (s ω : ℝ)) *
        (-(∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν)) := by
    have h :=
      avram_b80_original_jumpfree_cell_smallband_compensator_increment
        X n (s ω) (t ω) (hOrder ω) ω (hNoJump ω)
    rw [h]
    ring
  have hSourceLimit : Tendsto (fun n : ℕ =>
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n (t ω) ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n (s ω) ω)
      atTop (𝓝 (Jsmall (t ω) ω - Jsmall (s ω) ω)) :=
    (hJlim ω (t ω)).sub (hJlim ω (s ω))
  have hLimitMoment : Tendsto (fun n : ℕ =>
      ((t ω : ℝ) - (s ω : ℝ)) *
        (-(∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν)))
      atTop (𝓝 (((t ω : ℝ) - (s ω : ℝ)) * d)) :=
    tendsto_const_nhds.mul hνlim
  have hSeq : (fun n : ℕ =>
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n (t ω) ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n (s ω) ω) =
      (fun n : ℕ => ((t ω : ℝ) - (s ω : ℝ)) *
        (-(∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν))) := by
    funext n
    exact hCut n
  rw [hSeq] at hSourceLimit
  have hEq := tendsto_nhds_unique hSourceLimit hLimitMoment
  nlinarith
