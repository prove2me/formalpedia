-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.fluid_limit_of_finite_cost
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:30:35.543528+00:00
-- url     : https://prove2.me/submissions/dba7bf60-d8fc-4f11-ae53-b873a6fb1cd5

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_fluid_allocations_from_vanishing_queues
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_fluid_queue_vanishes_from_bounded_cost
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_primitive_fluid_limits_in_prob

open BellWilliams2001.ThresholdPolicy
open MeasureTheory Filter Topology Set
open scoped ENNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (T : ℕ → Allocation Ω) (hT : ∀ n, M.IsAdmissible n (T n))
    (hfin : liminf (fun n => M.cost n (T n)) atTop < ⊤)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (fun n => M.cost (φ n) (T (φ n))) atTop
      (𝓝 (liminf (fun n => M.cost n (T n)) atTop))) :
    UocInProb M.P (fun n ω t => M.Qbar (φ n) (T (φ n)) ω t) (fun _ => 0) ∧
    UocInProb M.P (fun n ω t => M.Abar (φ n) ω t) (fun t k => M.lam k * t) ∧
    UocInProb M.P (fun n ω t => M.Sbar (φ n) ω t) (fun t j => M.mu j * t) ∧
    UocInProb M.P (fun n ω t => M.Tbar (φ n) (T (φ n)) ω t) M.fluidAllocation ∧
    UocInProb M.P (fun n ω t => M.Ibar (φ n) (T (φ n)) ω t) (fun _ => 0) := by
  let L := liminf (fun n => M.cost n (T n)) atTop
  let B := L.toReal+1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hL : L < ENNReal.ofReal B := (ENNReal.lt_ofReal_iff_toReal_lt hfin.ne).2 (by dsimp [B]; linarith)
  have hCost : ∀ᶠ n in atTop, M.cost (φ n) (T (φ n)) ≤ ENNReal.ofReal B :=
    (hlim.eventually_lt_const hL).mono (fun _ h => h.le)
  have hAd : ∀ᶠ n in atTop, M.IsAdmissible (φ n) (T (φ n)) := Eventually.of_forall (fun n => hT (φ n))
  have hQ := fluid_queue_vanishes_from_bounded_cost M φ hφ.tendsto_atTop (T ∘ φ) hAd B hB hCost
  obtain ⟨hTa,hI⟩ := fluid_allocations_from_vanishing_queues M φ hφ.tendsto_atTop (T ∘ φ) hAd hQ
  obtain ⟨hA,hS⟩ := primitive_fluid_limits_in_prob M
  exact ⟨hQ,fun t ht ε hε => (hA t ht ε hε).comp hφ.tendsto_atTop,
    fun t ht ε hε => (hS t ht ε hε).comp hφ.tendsto_atTop,hTa,hI⟩
