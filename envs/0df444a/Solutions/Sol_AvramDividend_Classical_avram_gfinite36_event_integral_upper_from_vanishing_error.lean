-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite36_event_integral_upper_from_vanishing_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T10:52:51.901119+00:00
-- url     : https://prove2.me/submissions/f70a77ec-328e-47cb-8e28-9cea52a48043

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- A centred approximating residual and a vanishing integrated error
give the physical payoff's eventwise expectation budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (A : Set Ω) (b : ℝ) (F : Ω → ℝ)
    (M E : ℕ → Ω → ℝ)
    (hFI : IntegrableOn F A P)
    (hMI : ∀ n, IntegrableOn (M n) A P)
    (hEI : ∀ n, IntegrableOn (E n) A P)
    (hMean : ∀ n, (∫ ω in A, M n ω ∂P) = 0)
    (hUpper : ∀ n, ∀ᵐ ω ∂(P.restrict A),
      F ω ≤ b + M n ω + E n ω)
    (hErr : Tendsto (fun n => ∫ ω in A, E n ω ∂P) atTop (𝓝 (0 : ℝ))) :
    (∫ ω in A, F ω ∂P) ≤ ∫ ω in A, (b : ℝ) ∂P := by
  have hCI : IntegrableOn (fun _ : Ω => b) A P := integrableOn_const
  have hEach (n : ℕ) :
      (∫ ω in A, F ω ∂P) ≤
        (∫ ω in A, (b : ℝ) ∂P) +
          (∫ ω in A, E n ω ∂P) := by
    have hBE : IntegrableOn
        (fun ω => b + M n ω + E n ω) A P :=
      (hCI.add (hMI n)).add (hEI n)
    have hLe : (∫ ω in A, F ω ∂P) ≤
        ∫ ω in A, b + M n ω + E n ω ∂P :=
      integral_mono_ae hFI hBE (hUpper n)
    have hEq :
        (∫ ω in A, b + M n ω + E n ω ∂P) =
          (∫ ω in A, (b : ℝ) ∂P) +
            (∫ ω in A, E n ω ∂P) := by
      have hFirst :
          (∫ ω in A, b + M n ω + E n ω ∂P) =
            (∫ ω in A, b + M n ω ∂P) +
              (∫ ω in A, E n ω ∂P) := by
        simpa only [Pi.add_apply] using
          (integral_add (hCI.add (hMI n)) (hEI n))
      have hSecond :
          (∫ ω in A, b + M n ω ∂P) =
            (∫ ω in A, (b : ℝ) ∂P) +
              (∫ ω in A, M n ω ∂P) := by
        simpa only [Pi.add_apply] using
          (integral_add hCI (hMI n))
      rw [hFirst, hSecond, hMean n]
      ring
    rw [hEq] at hLe
    exact hLe
  have hLimit :
      (∫ ω in A, F ω ∂P) -
        (∫ ω in A, (b : ℝ) ∂P) ≤ 0 := by
    apply ge_of_tendsto hErr
    exact Filter.Eventually.of_forall (by
      intro n
      linarith [hEach n])
  linarith
