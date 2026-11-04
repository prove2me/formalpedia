-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_sigma_zero_ae_original_stopped_residual_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T11:00:07.292001+00:00
-- url     : https://prove2.me/submissions/96dde1a5-7c73-428a-92e0-200f13a65a85

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_nojump_nogaussian_drift_increment_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Pure-jump unbounded variation needs no Brownian motion: the original
same-space Gaussian residual vanishes a.s. on a genuine stopped interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (hσ : X.σ = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (X.X (τ ω + h) ω - ((τ ω + h) : ℝ) * X.c -
        Jsmall (τ ω + h) ω - Jlarge (τ ω + h) ω) -
      (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
        Jsmall (τ ω) ω - Jlarge (τ ω) ω) = 0 := by
  have hYσ0 : Y.σ = 0 := hYσ.trans hσ
  have hYzero :=
    avram_wave5_03a_actual_rightCont_stopped_nojump_nogaussian_drift_increment_ae
      Y hYν hYσ0 τ hτ T hbounded h
  filter_upwards [hSourceDecomp, hYzero] with ω hω hz
  calc
    (X.X (τ ω + h) ω - ((τ ω + h) : ℝ) * X.c -
        Jsmall (τ ω + h) ω - Jlarge (τ ω + h) ω) -
      (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
        Jsmall (τ ω) ω - Jlarge (τ ω) ω) =
      Y.X (τ ω + h) ω - Y.X (τ ω) ω - (h : ℝ) * Y.c := by
        rw [hω (τ ω + h), hω (τ ω)]
        push_cast
        ring
    _ = 0 := hz
