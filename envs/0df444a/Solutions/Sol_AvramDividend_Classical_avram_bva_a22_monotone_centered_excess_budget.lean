-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_monotone_centered_excess_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:03:06.917614+00:00
-- url     : https://prove2.me/submissions/af23a95c-2279-4579-b701-35e783afb011

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F N : ℕ → Ω → ℝ) (c : ℝ)
    (hF : ∀ m, Integrable (F m) P)
    (hN : ∀ m, Integrable (N m) P)
    (hNzero : ∀ m, (∫ ω, N m ω ∂P) = 0)
    (hMono : Monotone (fun m => ∫ ω, F m ω ∂P))
    (hExcess : Tendsto
      (fun m => ∫ ω, max (F m ω - (c + N m ω)) 0 ∂P)
      atTop (𝓝 (0 : ℝ))) :
    ∀ k : ℕ, (∫ ω, F k ω ∂P) ≤ c := by
  intro k
  have hlev (m : ℕ) :
      (∫ ω, F m ω ∂P) - c ≤
        ∫ ω, max (F m ω - (c + N m ω)) 0 ∂P := by
    have hC : Integrable (fun _ : Ω => c) P := integrable_const c
    have hBase : Integrable (fun ω => c + N m ω) P :=
      hC.add (hN m)
    have hR : Integrable (fun ω => F m ω - (c + N m ω)) P :=
      (hF m).sub hBase
    have hPos : Integrable
        (fun ω => max (F m ω - (c + N m ω)) 0) P :=
      hR.pos_part
    have hle :
        (∫ ω, F m ω - (c + N m ω) ∂P) ≤
          (∫ ω, max (F m ω - (c + N m ω)) 0 ∂P) :=
      integral_mono hR hPos (fun ω => le_max_left _ _)
    have heq : (∫ ω, F m ω - (c + N m ω) ∂P) =
        (∫ ω, F m ω ∂P) - c := by
      rw [integral_sub (hF m) hBase, integral_add hC (hN m)]
      simp [hNzero m]
    rw [heq] at hle
    exact hle
  have hlim : Tendsto
      (fun m => c + ∫ ω, max (F m ω - (c + N m ω)) 0 ∂P)
      atTop (𝓝 (c + 0)) :=
    tendsto_const_nhds.add hExcess
  have hEv : ∀ᶠ m in atTop,
      (∫ ω, F k ω ∂P) ≤
        c + ∫ ω, max (F m ω - (c + N m ω)) 0 ∂P := by
    filter_upwards [eventually_ge_atTop k] with m hkm
    have hm : (∫ ω, F k ω ∂P) ≤ (∫ ω, F m ω ∂P) :=
      hMono hkm
    linarith [hlev m]
  have hResult := ge_of_tendsto hlim hEv
  simpa using hResult
