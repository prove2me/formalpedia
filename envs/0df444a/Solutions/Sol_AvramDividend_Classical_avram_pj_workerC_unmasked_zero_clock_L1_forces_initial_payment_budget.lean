-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_unmasked_zero_clock_L1_forces_initial_payment_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:36:36.050746+00:00
-- url     : https://prove2.me/submissions/1c48f31e-be21-4337-9271-10edf805050a

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (A : Set Ω) (hA : MeasurableSet A)
    (K Q : Ω → ℝ)
    (hKI : Integrable K P) (hQI : Integrable Q P)
    (hResidual : ∀ᵐ ω ∂P, ω ∈ A → K ω + Q ω = 0)
    (ε : ℝ) (hKsmall : (∫ ω, |K ω| ∂P) ≤ ε) :
    (∫ ω in A, |Q ω| ∂P) ≤ ε := by 
  have hInd : Integrable (A.indicator (fun ω => |Q ω|)) P :=
    hQI.abs.indicator hA
  have hUpper :
      (∫ ω, A.indicator (fun ω => |Q ω|) ω ∂P) ≤
        ∫ ω, |K ω| ∂P := by
    apply integral_mono_ae hInd hKI.abs
    filter_upwards [hResidual] with ω hr
    by_cases ha : ω ∈ A
    · rw [Set.indicator_of_mem ha]
      have hq : Q ω = -K ω := by linarith [hr ha]
      rw [hq, abs_neg]
    · rw [Set.indicator_of_notMem ha]
      exact abs_nonneg _
  rw [integral_indicator hA] at hUpper
  exact hUpper.trans hKsmall
