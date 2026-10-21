-- Prove2me | solution 1 for FairProxy.ClosedFormDD.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:59:57.689684+00:00
-- url     : https://prove2.me/submissions/36393cc5-fa7f-4470-bc7f-6568353a4bb7

import Mathlib
import Definitions.Def_FairProxy_ClosedFormDD_Coupling

set_option autoImplicit false
open FairProxy.ClosedFormDD

theorem solution {S T : Type*} [Fintype S] [Fintype T]
    (σ : S → ℝ) (τ : T → ℝ)
    (hσ_nonneg : ∀ s, 0 ≤ σ s) (hτ_nonneg : ∀ t, 0 ≤ τ t)
    (hσ_sum : ∑ s, σ s = 1) (hτ_sum : ∑ t, τ t = 1) :
    couplingSet σ τ =
      {π | (∀ s, ∑ t, π s t = σ s) ∧
           (∀ t, ∑ s, π s t = τ t) ∧
           ∀ s t, max (σ s + τ t - 1) 0 ≤ π s t ∧
             π s t ≤ min (σ s) (τ t)} := by
  classical
  ext π
  simp only [couplingSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hr, hc, hb⟩
    refine ⟨hr, hc, fun s t => ⟨?_, ?_⟩⟩
    · refine max_le ?_ (hb s t).1
      -- 1 - σ s = ∑_{s' ≠ s} σ s' ≥ ∑_{s'≠s} π s' t = τ t - π s t
      have h1 : σ s + ∑ s' ∈ Finset.univ.erase s, σ s' = 1 := by
        rw [← hσ_sum]; exact (Finset.add_sum_erase Finset.univ σ (Finset.mem_univ s))
      have h2 : π s t + ∑ s' ∈ Finset.univ.erase s, π s' t = τ t := by
        rw [← hc t]; exact (Finset.add_sum_erase Finset.univ (fun s' => π s' t) (Finset.mem_univ s))
      have h3 : ∑ s' ∈ Finset.univ.erase s, π s' t ≤ ∑ s' ∈ Finset.univ.erase s, σ s' := by
        apply Finset.sum_le_sum
        intro s' _
        rw [← hr s']
        have := Finset.single_le_sum (f := fun t' : T => π s' t') (fun t' _ => (hb s' t').1)
          (Finset.mem_univ t)
        simpa using this
      linarith
    · refine le_min ?_ ?_
      · rw [← hr s]
        have := Finset.single_le_sum (f := fun t' : T => π s t') (fun t' _ => (hb s t').1)
          (Finset.mem_univ t)
        simpa using this
      · rw [← hc t]
        have := Finset.single_le_sum (f := fun s' : S => π s' t) (fun s' _ => (hb s' t).1)
          (Finset.mem_univ s)
        simpa using this
  · rintro ⟨hr, hc, hb⟩
    refine ⟨hr, hc, fun s t => ⟨le_trans (le_max_right _ _) (hb s t).1, ?_⟩⟩
    have hσ1 : σ s ≤ 1 := by
      rw [← hσ_sum]
      exact Finset.single_le_sum (f := σ) (fun s' _ => hσ_nonneg s') (Finset.mem_univ s)
    exact le_trans (hb s t).2 (le_trans (min_le_left _ _) hσ1)
