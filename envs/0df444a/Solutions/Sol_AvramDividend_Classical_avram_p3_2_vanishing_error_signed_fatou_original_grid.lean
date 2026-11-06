-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_vanishing_error_signed_fatou_original_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:23:43.324198+00:00
-- url     : https://prove2.me/submissions/ec259072-e5d1-441e-ba1a-4b023c4eb6ce

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_nonnegative_signed_fatou_prebudget_bridge
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Vanishing physical-mesh upper errors preserve the signed original BV
Fatou expectation budget without a globally dominating error envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (K : ℝ) (Y : Ω → ℝ) (F R : ℕ → Ω → ℝ)
    (ε : ℕ → ℝ)
    (hYInt : Integrable Y P) (hYNonneg : 0 ≤ᵐ[P] Y)
    (hFMeas : ∀ n, Measurable (F n))
    (hFInt : ∀ n, Integrable (F n) P)
    (hFNonneg : ∀ n, 0 ≤ᵐ[P] F n)
    (hR : ∀ n, Integrable (R n) P ∧ (∫ ω, R n ω ∂P) ≤ 0)
    (hErr : Tendsto ε atTop (nhds (0 : ℝ)))
    (hBound : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ K + R n ω + ε n)
    (hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Y ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    (∫ ω, Y ω ∂P) ≤ K := by
  have hBudget (δ : ℝ) (hδ : 0 < δ) :
      (∫ ω, Y ω ∂P) ≤ K + δ := by
    have hEventually : ∀ᶠ n in atTop, ε n < δ :=
      hErr.eventually_lt_const hδ
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hEventually
    have hBoundTail (n : ℕ) :
        ∀ᵐ ω ∂P, F (n + N) ω ≤ (K + δ) + R (n + N) ω := by
      filter_upwards [hBound (n + N)] with ω hω
      have hNN : N ≤ n + N := by omega
      have hε : ε (n + N) < δ := hN (n + N) hNN
      linarith
    have hFatouTail : ∀ᵐ ω ∂P,
        ENNReal.ofReal (Y ω) ≤
          liminf (fun n => ENNReal.ofReal (F (n + N) ω)) atTop := by
      filter_upwards [hFatou] with ω hω
      have hlim :
          liminf (fun n => ENNReal.ofReal (F (n + N) ω)) atTop =
            liminf (fun n => ENNReal.ofReal (F n ω)) atTop :=
        Filter.liminf_nat_add (fun n => ENNReal.ofReal (F n ω)) N
      rw [hlim]
      exact hω
    exact AvramDividend.Classical.avram_p3_2_nonnegative_signed_fatou_prebudget_bridge
      P (K + δ) Y (fun n => F (n + N)) (fun n => R (n + N))
      hYInt hYNonneg (fun n => hFMeas (n + N))
      (fun n => hFInt (n + N)) (fun n => hFNonneg (n + N))
      (fun n => hR (n + N)) hBoundTail hFatouTail
  by_contra hn
  have hδ : 0 < ((∫ ω, Y ω ∂P) - K) / 2 := by
    have : K < ∫ ω, Y ω ∂P := lt_of_not_ge hn
    linarith
  have h := hBudget _ hδ
  linarith
