-- Prove2me | solution 1 for AvramDividend.Classical.avram_residual14_positive_mean_deficit_centring_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:59:36.209486+00:00
-- url     : https://prove2.me/submissions/a538c759-8dc1-4c28-9cda-a0f20b85da04

import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
noncomputable section

/-- A fixed positive expected deficit cannot be covered by centred
    integrable terms and positive errors vanishing in expectation. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (G : Ω → ℝ) (hG : Integrable G P)
    (hGPos : 0 < ∫ ω, G ω ∂P)
    (M Err : ℕ → Ω → ℝ)
    (hM : ∀ n, Integrable (M n) P ∧
      (∫ ω, M n ω ∂P) = 0)
    (hErr : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hErr0 : Tendsto
      (fun n => ∫ ω, max (Err n ω) 0 ∂P)
      atTop (nhds (0 : ℝ)))
    (hLower : ∀ n, ∀ᵐ ω ∂P,
      G ω ≤ M n ω + max (Err n ω) 0) :
    False := by
  have hIntegral (n : ℕ) :
      (∫ ω, G ω ∂P) ≤
        (∫ ω, max (Err n ω) 0 ∂P) := by
    calc
      (∫ ω, G ω ∂P) ≤
          (∫ ω, M n ω + max (Err n ω) 0 ∂P) :=
        integral_mono_ae hG ((hM n).1.add (hErr n)) (hLower n)
      _ = (∫ ω, M n ω ∂P) +
          (∫ ω, max (Err n ω) 0 ∂P) :=
        integral_add (hM n).1 (hErr n)
      _ = (∫ ω, max (Err n ω) 0 ∂P) := by
        rw [(hM n).2, zero_add]
  have hSmall : ∀ᶠ n : ℕ in atTop,
      (∫ ω, max (Err n ω) 0 ∂P) <
        (∫ ω, G ω ∂P) := by
    exact hErr0.eventually (isOpen_Iio.mem_nhds hGPos)
  obtain ⟨n, hn⟩ := hSmall.exists
  exact (not_le_of_gt hn) (hIntegral n)
