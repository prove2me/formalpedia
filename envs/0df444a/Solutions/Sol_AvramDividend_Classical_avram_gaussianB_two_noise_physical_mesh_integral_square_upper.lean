-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_two_noise_physical_mesh_integral_square_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:46:46.700184+00:00
-- url     : https://prove2.me/submissions/dfbb597a-0cb7-421e-ad96-89188f9a5410

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section
/-- Two-channel Gaussian physical mesh squared-error integral bound. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (L Q : ℕ → Ω → ℝ)
    (hLInt : ∀ m l, Integrable (fun ω => (L m ω - L l ω) ^ 2) P)
    (hQInt : ∀ m, Integrable (fun ω => (Q m ω) ^ 2) P)
    (hMInt : ∀ m l, Integrable (fun ω =>
      ((L m ω + Q m ω) - (L l ω + Q l ω)) ^ 2) P) :
    ∀ m l,
      (∫ ω, ((L m ω + Q m ω) -
        (L l ω + Q l ω)) ^ 2 ∂P) ≤
      2 * (∫ ω, (L m ω - L l ω) ^ 2 ∂P) +
      4 * (∫ ω, (Q m ω) ^ 2 ∂P) +
      4 * (∫ ω, (Q l ω) ^ 2 ∂P) := by
  intro m l
  have hRHS : Integrable (fun ω =>
      2 * (L m ω - L l ω) ^ 2 +
      4 * (Q m ω) ^ 2 + 4 * (Q l ω) ^ 2) P :=
    (((hLInt m l).const_mul 2).add ((hQInt m).const_mul 4)).add
      ((hQInt l).const_mul 4)
  have hPoint (ω : Ω) :
      ((L m ω + Q m ω) - (L l ω + Q l ω)) ^ 2 ≤
      2 * (L m ω - L l ω) ^ 2 +
      4 * (Q m ω) ^ 2 + 4 * (Q l ω) ^ 2 := by
    nlinarith [sq_nonneg ((L m ω - L l ω) -
      (Q m ω - Q l ω)), sq_nonneg (Q m ω + Q l ω)]
  calc
    (∫ ω, ((L m ω + Q m ω) -
      (L l ω + Q l ω)) ^ 2 ∂P) ≤
      ∫ ω, (2 * (L m ω - L l ω) ^ 2 +
        4 * (Q m ω) ^ 2 + 4 * (Q l ω) ^ 2) ∂P :=
        integral_mono (hMInt m l) hRHS hPoint
    _ = 2 * (∫ ω, (L m ω - L l ω) ^ 2 ∂P) +
      4 * (∫ ω, (Q m ω) ^ 2 ∂P) +
      4 * (∫ ω, (Q l ω) ^ 2 ∂P) := by
        have h1 :
            (∫ ω, (2 * (L m ω - L l ω) ^ 2 +
              4 * (Q m ω) ^ 2) + 4 * (Q l ω) ^ 2 ∂P) =
            (∫ ω, 2 * (L m ω - L l ω) ^ 2 +
              4 * (Q m ω) ^ 2 ∂P) +
            (∫ ω, 4 * (Q l ω) ^ 2 ∂P) := by
          simpa only [Pi.add_apply] using
            (integral_add (((hLInt m l).const_mul 2).add
              ((hQInt m).const_mul 4)) ((hQInt l).const_mul 4))
        have h2 :
            (∫ ω, 2 * (L m ω - L l ω) ^ 2 +
              4 * (Q m ω) ^ 2 ∂P) =
            (∫ ω, 2 * (L m ω - L l ω) ^ 2 ∂P) +
            (∫ ω, 4 * (Q m ω) ^ 2 ∂P) := by
          simpa only [Pi.add_apply] using
            (integral_add ((hLInt m l).const_mul 2)
              ((hQInt m).const_mul 4))
        rw [h1, h2]
        simp only [integral_const_mul]
