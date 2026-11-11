-- Prove2me | solution 1 for DecQueueLearning.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T06:08:57.943194+00:00
-- url     : https://prove2.me/submissions/afb45f33-3e28-4e6d-a34e-d58e65a72726

import Mathlib
import Definitions.Def_DecQueueLearning_CompSlack

open DecQueueLearning in
theorem solution {N K : ℕ} (α : ℝ) (hα : 0 < α) (w : Fin N → Fin K → ℝ)
    (σ : Fin N → Option (Fin K)) (hσ : IsMatching σ) (p : Fin K → ℝ) (π : Fin N → ℝ)
    (h : IsCompSlack α w σ p π) :
    (1 - α) * maxWeight w ≤ ∑ i, selWeight w σ i := by
  classical
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hp0 : ∀ j, 0 ≤ p j := by
    intro j
    by_cases hj : ∃ i, σ i = some j
    · exact h2 j hj
    · exact (h1 j hj).symm.le
  have hπ0 : ∀ i, 0 ≤ π i := fun i => (h3 i).2 (Set.mem_insert 0 _)
  have hw : ∀ i j, w i j ≤ π i + p j := by
    intro i j
    have := (h3 i).2 (Set.mem_insert_of_mem _ ⟨j, rfl⟩)
    linarith
  -- upper bound for every feasible ϕ
  have hbound : ∀ ϕ ∈ capacityRegion N K,
      ∑ i, ∑ j, w i j * ϕ i j ≤ ∑ i, π i + ∑ j, p j := by
    intro ϕ hϕ
    obtain ⟨hr, hc, hn⟩ := hϕ
    calc ∑ i, ∑ j, w i j * ϕ i j ≤ ∑ i, ∑ j, (π i * ϕ i j + p j * ϕ i j) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum fun j _ => by
            nlinarith [hw i j, hn i j])
      _ = ∑ i, π i * ∑ j, ϕ i j + ∑ j, p j * ∑ i, ϕ i j := by
          rw [Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib), Finset.sum_add_distrib,
            Finset.sum_comm (f := fun i j => p j * ϕ i j)]
          simp only [Finset.mul_sum]
      _ ≤ ∑ i, π i + ∑ j, p j :=
          add_le_add (Finset.sum_le_sum fun i _ => mul_le_of_le_one_right (hπ0 i) (hr i))
            (Finset.sum_le_sum fun j _ => mul_le_of_le_one_right (hp0 j) (hc j))
  have h0mem : (0 : Fin N → Fin K → ℝ) ∈ capacityRegion N K :=
    ⟨fun i => by simp, fun j => by simp, fun i j => le_refl 0⟩
  have hbdd : BddAbove ((fun ϕ : Fin N → Fin K → ℝ => ∑ i, ∑ j, w i j * ϕ i j) ''
      capacityRegion N K) := by
    refine ⟨∑ i, π i + ∑ j, p j, ?_⟩
    rintro y ⟨ϕ, hϕ, rfl⟩
    exact hbound ϕ hϕ
  have hM0 : 0 ≤ maxWeight w := by
    unfold maxWeight
    exact le_csSup_of_le hbdd ⟨0, h0mem, rfl⟩ (by simp)
  have hMle : maxWeight w ≤ ∑ i, π i + ∑ j, p j := by
    unfold maxWeight
    apply csSup_le (⟨_, ⟨0, h0mem, rfl⟩⟩ : Set.Nonempty
      ((fun ϕ : Fin N → Fin K → ℝ => ∑ i, ∑ j, w i j * ϕ i j) '' capacityRegion N K))
    rintro y ⟨ϕ, hϕ, rfl⟩
    exact hbound ϕ hϕ
  -- matching accounting
  have hpj : ∀ j, p j = ∑ i, if σ i = some j then p j else 0 := by
    intro j
    by_cases hj : ∃ i, σ i = some j
    · obtain ⟨i0, hi0⟩ := hj
      rw [Finset.sum_eq_single i0 (fun b _ hb => by
          rw [if_neg]
          intro hb'
          rcases hσ b i0 hb with hh | hh
          · rw [hh] at hb'; cases hb'
          · exact hh (hb'.trans hi0.symm)) (by simp)]
      rw [if_pos hi0]
    · rw [h1 j hj]; simp
  have hsump : ∑ j, p j = ∑ i, ∑ j, (if σ i = some j then p j else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => hpj j)
  have hper : ∀ i, π i + ∑ j, (if σ i = some j then p j else 0) ≤ (1 + α) * selWeight w σ i ∧
      0 ≤ selWeight w σ i := by
    intro i
    rcases hsi : σ i with _ | j
    · have e1 : selWeight w σ i = 0 := by simp [selWeight, hsi]
      rw [e1, h4 i hsi]
      simp
    · obtain ⟨hwp, hle⟩ := h5 i j hsi
      have e1 : selWeight w σ i = w i j := by simp [selWeight, hsi]
      have e2 : ∑ j', (if some j = some j' then p j' else 0) = p j := by simp
      rw [e1, e2]
      exact ⟨hle, hwp.le⟩
  have hA0 : 0 ≤ ∑ i, selWeight w σ i := Finset.sum_nonneg (fun i _ => (hper i).2)
  have hkey : ∑ i, π i + ∑ j, p j ≤ (1 + α) * ∑ i, selWeight w σ i := by
    rw [hsump, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => (hper i).1)
  rcases le_or_gt 1 α with hα1 | hα1
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_left (hMle.trans hkey) (show (0:ℝ) ≤ 1 - α by linarith),
      mul_nonneg (sq_nonneg α) hA0]
