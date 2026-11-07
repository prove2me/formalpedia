-- Prove2me | solution 1 for AvramDividend.Classical.avram_reuse8_nonintegrable_drift_grid_expected_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:40:32.092929+00:00
-- url     : https://prove2.me/submissions/a5dcf14b-5bd4-48cb-8fe1-1d4bab20f8bf

import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (b : ℝ) (F M B E : ℕ → Ω → ℝ)
    (hFmeas : ∀ n, Measurable (F n))
    (hFnonneg : ∀ n, 0 ≤ᵐ[P] F n)
    (hMI : ∀ n, Integrable (M n) P)
    (hM0 : ∀ n, (∫ ω, M n ω ∂P) = 0)
    (hEI : ∀ n, Integrable (fun ω => max (E n ω) 0) P)
    (hB : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0)
    (hPhysical : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ b + M n ω + B n ω + max (E n ω) 0) :
    ∀ n, Integrable (F n) P ∧
      (∫ ω, F n ω ∂P) ≤
        b + (∫ ω, max (E n ω) 0 ∂P) := by
  intro n
  have hUpperI : Integrable
      (fun ω => b + M n ω + max (E n ω) 0) P :=
    ((integrable_const b).add (hMI n)).add (hEI n)
  have hIneq : ∀ᵐ ω ∂P,
      F n ω ≤ b + M n ω + max (E n ω) 0 := by
    filter_upwards [hB n, hPhysical n] with ω hBω hPhys
    linarith
  have hNorm : ∀ᵐ ω ∂P,
      ‖F n ω‖ ≤ b + M n ω + max (E n ω) 0 := by
    filter_upwards [hFnonneg n, hIneq] with ω hNonneg hLe
    rwa [Real.norm_eq_abs, abs_of_nonneg hNonneg]
  have hFI : Integrable (F n) P :=
    hUpperI.mono' (hFmeas n).aestronglyMeasurable hNorm
  refine ⟨hFI, ?_⟩
  have hMono : (∫ ω, F n ω ∂P) ≤
      (∫ ω, b + M n ω + max (E n ω) 0 ∂P) :=
    integral_mono_ae hFI hUpperI hIneq
  have hIntegral :
      (∫ ω, b + M n ω + max (E n ω) 0 ∂P) =
        b + (∫ ω, max (E n ω) 0 ∂P) := by
    calc
      (∫ ω, b + M n ω + max (E n ω) 0 ∂P) =
          (∫ ω, b + M n ω ∂P) +
            (∫ ω, max (E n ω) 0 ∂P) :=
        integral_add ((integrable_const b).add (hMI n)) (hEI n)
      _ = ((∫ (_ : Ω), b ∂P) + (∫ ω, M n ω ∂P)) +
            (∫ ω, max (E n ω) 0 ∂P) :=
        congrArg (fun z : ℝ => z + (∫ ω, max (E n ω) 0 ∂P))
          (integral_add (integrable_const b) (hMI n))
      _ = b + (∫ ω, max (E n ω) 0 ∂P) := by
        simp [hM0 n]
  calc
    (∫ ω, F n ω ∂P) ≤
        (∫ ω, b + M n ω + max (E n ω) 0 ∂P) := hMono
    _ = b + (∫ ω, max (E n ω) 0 ∂P) := hIntegral
