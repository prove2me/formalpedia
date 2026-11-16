-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB54zz_event_restricted_zero_L1_limit_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:56:13.544335+00:00
-- url     : https://prove2.me/submissions/1d52a46b-39bc-4d09-b662-51ef9374e443

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (B : Set Ω) (hB : MeasurableSet B)
    (N : Ω → ℝ) (M : ℕ → Ω → ℝ)
    (hNI : Integrable N μ) (hMI : ∀ m, Integrable (M m) μ)
    (hZero : ∀ m ω, ω ∈ B → M m ω = 0)
    (hL : Tendsto (fun m => ∫ ω, |N ω - M m ω| ∂μ)
      atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂μ, ω ∈ B → N ω = 0 := by
  let ν : Measure Ω := μ.restrict B
  have hmono : ν ≤ μ := Measure.restrict_le_self
  have hNν : Integrable N ν := hNI.mono_measure hmono
  have hBzero (m : ℕ) :
      (∫ ω, |N ω| ∂ν) = ∫ ω, |N ω - M m ω| ∂ν := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hB] with ω hω
    rw [hZero m ω hω, sub_zero]
  have hUpper (m : ℕ) : (∫ ω, |N ω| ∂ν) ≤
      ∫ ω, |N ω - M m ω| ∂μ := by
    rw [hBzero m]
    exact integral_mono_measure hmono
      (Filter.Eventually.of_forall (fun ω => abs_nonneg (N ω - M m ω)))
      ((hNI.sub (hMI m)).abs)
  have hLe : (∫ ω, |N ω| ∂ν) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hL
      (Filter.Eventually.of_forall hUpper)
  have hEq : (∫ ω, |N ω| ∂ν) = 0 :=
    le_antisymm hLe (integral_nonneg (fun ω => abs_nonneg (N ω)))
  have hZeroAe : ∀ᵐ ω ∂ν, |N ω| = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall (fun ω => abs_nonneg (N ω))) hNν.abs).mp hEq
  exact (ae_restrict_iff' hB).mp
    (hZeroAe.mono (fun ω hω => abs_eq_zero.mp hω))
