-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb73_integral_L2_polarization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:21:31.215369+00:00
-- url     : https://prove2.me/submissions/221d7060-111e-4cef-872e-9bb32a68585f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- Polarise a real square under an integral, with all integrability explicit. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f g : Ω → ℝ)
    (hf2 : Integrable (fun ω => (f ω) ^ 2) P)
    (hg2 : Integrable (fun ω => (g ω) ^ 2) P)
    (hprod : Integrable (fun ω => f ω * g ω) P) :
    (∫ ω, (f ω - g ω) ^ 2 ∂P) =
      (∫ ω, (f ω) ^ 2 ∂P) + (∫ ω, (g ω) ^ 2 ∂P) -
        2 * (∫ ω, f ω * g ω ∂P) := by
  have heq : (fun ω => (f ω - g ω) ^ 2) =
      (fun ω => (f ω) ^ 2 + (g ω) ^ 2 - 2 * (f ω * g ω)) := by
    funext ω
    ring
  have hsub :
      (∫ ω, (f ω) ^ 2 + (g ω) ^ 2 - 2 * (f ω * g ω) ∂P) =
        (∫ ω, (f ω) ^ 2 + (g ω) ^ 2 ∂P) -
          (∫ ω, 2 * (f ω * g ω) ∂P) := by
    exact integral_sub (hf2.add hg2) (hprod.const_mul 2)
  rw [heq]
  calc
    _ = (∫ ω, (f ω) ^ 2 + (g ω) ^ 2 ∂P) -
          (∫ ω, 2 * (f ω * g ω) ∂P) := hsub
    _ = _ := by rw [integral_add hf2 hg2, integral_const_mul]
