-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_centered_physical_error_signed_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:44:39.976192+00:00
-- url     : https://prove2.me/submissions/19961a57-54b7-46d6-bd96-2bdc7939266b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

/-- The original stopped physical error can be centred without changing the
signed mean budget or requiring separate M and B integrability. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Z Err : ℕ → Ω → ℝ)
    (hZ : ∀ n, Integrable (Z n) P ∧
      (∫ ω, Z n ω ∂P) ≤ 0)
    (hErr : ∀ n, Integrable (Err n) P) :
    ∀ n,
      Integrable (fun ω => Z n ω + Err n ω -
        (∫ ξ, Err n ξ ∂P)) P ∧
      (∫ ω, Z n ω + Err n ω -
        (∫ ξ, Err n ξ ∂P) ∂P) ≤ 0 := by
  intro n
  have hSum : Integrable (fun ω => Z n ω + Err n ω) P :=
    (hZ n).1.add (hErr n)
  have hConst : Integrable (fun _ : Ω => (∫ ξ, Err n ξ ∂P)) P :=
    integrable_const _
  refine ⟨hSum.sub hConst, ?_⟩
  calc
    (∫ ω, Z n ω + Err n ω -
        (∫ ξ, Err n ξ ∂P) ∂P) =
        (∫ ω, Z n ω ∂P) := by
      rw [integral_sub hSum hConst, integral_add (hZ n).1 (hErr n)]
      simp
    _ ≤ 0 := (hZ n).2
