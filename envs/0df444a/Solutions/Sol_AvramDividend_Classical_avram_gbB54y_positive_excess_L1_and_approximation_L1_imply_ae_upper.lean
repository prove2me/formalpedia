-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB54y_positive_excess_L1_and_approximation_L1_imply_ae_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:52:12.616673+00:00
-- url     : https://prove2.me/submissions/2e50f0f4-8888-4194-acc5-fb0f308b2bc1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (K N : Ω → ℝ) (M : ℕ → Ω → ℝ)
    (hKI : Integrable K μ) (hNI : Integrable N μ)
    (hMI : ∀ m, Integrable (M m) μ)
    (hRes : Tendsto (fun m => ∫ ω, max (K ω - M m ω) 0 ∂μ)
      atTop (nhds (0 : ℝ)))
    (hDiff : Tendsto (fun m => ∫ ω, |N ω - M m ω| ∂μ)
      atTop (nhds (0 : ℝ))) :
    ∀ᵐ ω ∂μ, K ω ≤ N ω := by
  have hQI : Integrable (fun ω => max (K ω - N ω) 0) μ :=
    (hKI.sub hNI).sup (integrable_zero Ω ℝ μ)
  have hRI (m : ℕ) : Integrable (fun ω => max (K ω - M m ω) 0) μ :=
    (hKI.sub (hMI m)).sup (integrable_zero Ω ℝ μ)
  have hDI (m : ℕ) : Integrable (fun ω => |N ω - M m ω|) μ :=
    (hNI.sub (hMI m)).abs
  have hPoint (m : ℕ) (ω : Ω) :
      max (K ω - N ω) 0 ≤ max (K ω - M m ω) 0 + |N ω - M m ω| := by
    have hL : K ω - M m ω ≤ max (K ω - M m ω) 0 := le_max_left _ _
    have h0 : 0 ≤ max (K ω - M m ω) 0 := le_max_right _ _
    have hAbs : M m ω - N ω ≤ |N ω - M m ω| := by
      have hh := neg_le_abs (N ω - M m ω)
      linarith
    exact max_le (by linarith) (by linarith [abs_nonneg (N ω - M m ω)])
  have hBound (m : ℕ) : (∫ ω, max (K ω - N ω) 0 ∂μ) ≤
      (∫ ω, max (K ω - M m ω) 0 ∂μ) +
      (∫ ω, |N ω - M m ω| ∂μ) := by
    calc
      _ ≤ ∫ ω, max (K ω - M m ω) 0 + |N ω - M m ω| ∂μ := by
        apply integral_mono_ae hQI ((hRI m).add (hDI m))
        exact Filter.Eventually.of_forall (hPoint m)
      _ = _ := integral_add (hRI m) (hDI m)
  have hQ0 : (∫ ω, max (K ω - N ω) 0 ∂μ) = 0 := by
    apply le_antisymm
    · have hSum : Tendsto
          (fun m => (∫ ω, max (K ω - M m ω) 0 ∂μ) +
            (∫ ω, |N ω - M m ω| ∂μ)) atTop (nhds (0 : ℝ)) := by
        simpa using hRes.add hDiff
      exact le_of_tendsto_of_tendsto tendsto_const_nhds hSum
        (Filter.Eventually.of_forall hBound)
    · exact integral_nonneg (fun ω => le_max_right _ _)
  have hAE : ∀ᵐ ω ∂μ, max (K ω - N ω) 0 = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall (fun ω => le_max_right _ _)) hQI).mp hQ0
  filter_upwards [hAE] with ω hω
  have hle := le_max_left (K ω - N ω) (0 : ℝ)
  rw [hω] at hle
  linarith
