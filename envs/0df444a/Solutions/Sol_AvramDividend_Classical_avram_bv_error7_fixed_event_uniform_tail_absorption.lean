-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_fixed_event_uniform_tail_absorption
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T13:17:22.765794+00:00
-- url     : https://prove2.me/submissions/13fc6493-399c-4930-8168-d8961938fcc2

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_positive_error_measurable_event_split
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Metric AvramDividend.Classical
open scoped Classical
noncomputable section

/-- Vanishing positive-error means on every fixed interior localisation,
combined with a uniform integrable complement-tail estimate, imply
unlocalised vanishing expected error. This is the two-limit absorption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (s : ℕ → Set Ω) (hs : ∀ n, MeasurableSet (s n))
    (Err : ℕ → Ω → ℝ)
    (hPos : ∀ m, Integrable (fun ω => max (Err m ω) 0) P)
    (hLocal : ∀ n, Tendsto
      (fun m => ∫ ω, max (if ω ∈ s n then Err m ω else 0) 0 ∂P)
      atTop (nhds (0 : ℝ)))
    (tail : ℕ → ℝ)
    (hTail : Tendsto tail atTop (nhds (0 : ℝ)))
    (hTailBound : ∀ n m,
      (∫ ω, max (if ω ∉ s n then Err m ω else 0) 0 ∂P) ≤ tail n) :
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨n, hn'⟩ := (Metric.tendsto_atTop.1 hTail) (ε / 2) hε2
  have hn : dist (tail n) 0 < ε / 2 := hn' n le_rfl
  obtain ⟨M, hM⟩ :=
    (Metric.tendsto_atTop.1 (hLocal n)) (ε / 2) hε2
  refine ⟨M, ?_⟩
  intro m hm
  have hm' : dist
      (∫ ω, max (if ω ∈ s n then Err m ω else 0) 0 ∂P)
      0 < ε / 2 := hM m hm
  have hSum :=
    (avram_bv_error7_positive_error_measurable_event_split
      P (s n) (hs n) (Err m) (hPos m)).2.2
  have hNonneg : 0 ≤ ∫ ω, max (Err m ω) 0 ∂P := by
    apply integral_nonneg
    intro ω
    exact le_max_right _ _
  have hTailSmall : tail n < ε / 2 := by
    have hh : |tail n| < ε / 2 := by
      simpa only [Real.dist_eq, sub_zero] using hn
    exact lt_of_le_of_lt (le_abs_self _) hh
  have hLocSmall :
      (∫ ω, max (if ω ∈ s n then Err m ω else 0) 0 ∂P) < ε / 2 := by
    have hh :
        |∫ ω, max (if ω ∈ s n then Err m ω else 0) 0 ∂P| <
          ε / 2 := by
      simpa only [Real.dist_eq, sub_zero] using hm'
    exact lt_of_le_of_lt (le_abs_self _) hh
  have hBound :
      (∫ ω, max (Err m ω) 0 ∂P) ≤
        (∫ ω, max (if ω ∈ s n then Err m ω else 0) 0 ∂P) + tail n := by
    calc
      (∫ ω, max (Err m ω) 0 ∂P) =
        (∫ ω, max (if ω ∈ s n then Err m ω else 0) 0 ∂P) +
        (∫ ω, max (if ω ∉ s n then Err m ω else 0) 0 ∂P) := hSum
      _ ≤ (∫ ω, max (if ω ∈ s n then Err m ω else 0) 0 ∂P) +
        tail n := by linarith [hTailBound n m]
  have hSmall : (∫ ω, max (Err m ω) 0 ∂P) < ε := by
    linarith
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hNonneg] using hSmall
