-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_persistent_integrable_positive_witness_forbids_spatial_L1_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T13:01:57.259587+00:00
-- url     : https://prove2.me/submissions/64fe8fae-4c28-46c1-890b-fbc8db311a01

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter
open scoped Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hEI : ∀ m, Integrable (fun ω => max (E m ω) 0) P)
    (hgI : Integrable g P)
    (hgpos : 0 < ∫ ω, g ω ∂P)
    (hbound : ∀ᶠ m : ℕ in atTop, ∀ᵐ ω ∂P,
      g ω ≤ max (E m ω) 0) :
    ¬ Tendsto (fun m => ∫ ω, max (E m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  intro hlim
  have hsmall : ∀ᶠ m : ℕ in atTop,
      (∫ ω, max (E m ω) 0 ∂P) < ∫ ω, g ω ∂P :=
    hlim.eventually (Iio_mem_nhds hgpos)
  obtain ⟨m, hm, hs⟩ := (hbound.and hsmall).exists
  have hle : (∫ ω, g ω ∂P) ≤
      (∫ ω, max (E m ω) 0 ∂P) :=
    integral_mono_ae hgI (hEI m) hm
  exact (not_lt_of_ge hle) hs