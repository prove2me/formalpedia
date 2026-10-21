-- Prove2me | solution 1 for DelayDep.Equiv.pathwise_coupling
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T09:18:14.023006+00:00
-- url     : https://prove2.me/submissions/97ff8dd6-fdc3-4d82-a43e-59e74d02c645

import Mathlib
import Definitions.Def_DelayDep_Equiv_Model

open DelayDep.Equiv
open scoped Classical

theorem solution {n : ℕ} [NeZero n] (α : ℕ → ℝ) (u : Fin n → ℝ)
    (tp tp' : ℕ → ℝ) (sv sv' : ℕ → ℝ → ℝ)
    (h_served : ∀ i, wait α u tp sv i ≤ tp i ↔ wait α u tp sv i ≤ tp' i)
    (h_service : ∀ i, wait α u tp sv i ≤ tp i →
      sv' i (wait α u tp sv i) = sv i (wait α u tp sv i))
    (h_abandon : ∀ i, ¬ wait α u tp sv i ≤ tp i → tp' i = tp i) :
    (∀ i, Zvec α u tp' sv' i = Zvec α u tp sv i) ∧
      ∀ τ : NNReal, pathX α u tp' sv' τ = pathX α u tp sv τ := by
  have hZ : ∀ i, Zvec α u tp' sv' i = Zvec α u tp sv i := by
    intro i
    induction i with
    | zero => rfl
    | succ k ih =>
      show sortR _ = sortR _
      congr 1
      funext j
      rw [ih]
      have hs := h_served k
      have hv := h_service k
      simp only [wait] at hs hv
      by_cases h : Zvec α u tp sv k 0 ≤ tp k
      · rw [if_pos (hs.mp h), if_pos h, hv h]
      · rw [if_neg (fun h' => h (hs.mpr h')), if_neg h]
  have hw : ∀ i, wait α u tp' sv' i = wait α u tp sv i := fun i => by simp only [wait, hZ]
  refine ⟨hZ, fun τ => ?_⟩
  have hS : ∀ i, inService α u tp' sv' τ i ↔ inService α u tp sv τ i := by
    intro i
    simp only [inService, served, hw]
    constructor
    · rintro ⟨a, b, c, d⟩
      have b' := (h_served i).mpr b
      exact ⟨a, b', c, by rwa [h_service i b'] at d⟩
    · rintro ⟨a, b, c, d⟩
      exact ⟨a, (h_served i).mp b, c, by rwa [h_service i b]⟩
  have hQ : ∀ i, inQueue α u tp' sv' τ i ↔ inQueue α u tp sv τ i := by
    intro i
    simp only [inQueue, hw]
    by_cases h : wait α u tp sv i ≤ tp i
    · rw [min_eq_right h, min_eq_right ((h_served i).mp h)]
    · rw [h_abandon i h]
  have hR : remainingList α u tp' sv' τ = remainingList α u tp sv τ := by
    simp only [remainingList]
    have hfilt : (List.range (nextArr α τ)).filter (fun i => decide (inService α u tp' sv' τ i)) =
        (List.range (nextArr α τ)).filter (fun i => decide (inService α u tp sv τ i)) := by
      congr 1; funext i; simp only [hS i]
    rw [hfilt]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [List.mem_filter] at hi
    have hi2 : inService α u tp sv τ i := of_decide_eq_true hi.2
    rw [hw, h_service i hi2.2.1]
  have hW : waitingList α u tp' sv' τ = waitingList α u tp sv τ := by
    simp only [waitingList]
    congr 1
    congr 1; funext i; simp only [hQ i]
  simp only [pathX, hR, hW]
