-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_signed_fatou_integrable_residual_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:08:03.232426+00:00
-- url     : https://prove2.me/submissions/20b09e66-8aed-43e1-9a79-f669996cacf0

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_nonnegative_signed_fatou_prebudget_bridge

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- A signed original-process grid yields a genuine integrable residual
without appealing to any canonical strict budget as a hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (K : ℝ) (Y : Ω → ℝ)
    (F R : ℕ → Ω → ℝ)
    (hYInt : Integrable Y P)
    (hYNonneg : 0 ≤ᵐ[P] Y)
    (hFMeas : ∀ n, Measurable (F n))
    (hFInt : ∀ n, Integrable (F n) P)
    (hFNonneg : ∀ n, 0 ≤ᵐ[P] F n)
    (hR : ∀ n, Integrable (R n) P ∧
      (∫ ω, R n ω ∂P) ≤ 0)
    (hBound : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ K + R n ω)
    (hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Y ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    ∃ E : Ω → ℝ, Integrable E P ∧
      (∫ ω, E ω ∂P) ≤ 0 ∧
      (∀ᵐ ω ∂P, Y ω ≤ K + E ω) := by
  have hBudget : (∫ ω, Y ω ∂P) ≤ K :=
    AvramDividend.Classical.avram_p3_2_nonnegative_signed_fatou_prebudget_bridge
      P K Y F R hYInt hYNonneg hFMeas hFInt hFNonneg
      hR hBound hFatou
  have hEInt : Integrable (fun ω => Y ω - K) P :=
    hYInt.sub (integrable_const K)
  have hEMean : (∫ ω, Y ω - K ∂P) ≤ 0 := by
    rw [integral_sub hYInt (integrable_const K)]
    simp
    linarith only [hBudget]
  refine ⟨fun ω => Y ω - K, hEInt, hEMean, ?_⟩
  exact Filter.Eventually.of_forall (fun ω => by dsimp; linarith)
