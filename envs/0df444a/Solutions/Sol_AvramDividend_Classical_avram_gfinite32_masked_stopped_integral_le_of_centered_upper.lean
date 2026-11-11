-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite32_masked_stopped_integral_le_of_centered_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T07:59:46.691397+00:00
-- url     : https://prove2.me/submissions/3517cae2-c9cd-4b75-a31a-d828f2b52c31

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : Set Ω) (a : ℝ) (R M : Ω → ℝ)
    (hR : IntegrableOn R E P)
    (hM : IntegrableOn M E P)
    (hConst : IntegrableOn (fun _ : Ω => a) E P)
    (hMzero : (∫ ω in E, M ω ∂P) = 0)
    (hUpper : ∀ᵐ ω ∂(P.restrict E), R ω ≤ a + M ω) :
    (∫ ω in E, R ω ∂P) ≤ (∫ ω in E, a ∂P) := by
  have hSum : IntegrableOn (fun ω => a + M ω) E P := hConst.add hM
  have hBound :
      (∫ ω in E, R ω ∂P) ≤ (∫ ω in E, a + M ω ∂P) :=
    integral_mono_ae hR hSum hUpper
  calc
    (∫ ω in E, R ω ∂P) ≤ (∫ ω in E, a + M ω ∂P) := hBound
    _ = (∫ ω in E, a ∂P) + (∫ ω in E, M ω ∂P) := by
      exact integral_add hConst hM
    _ = (∫ ω in E, a ∂P) := by rw [hMzero, add_zero]
