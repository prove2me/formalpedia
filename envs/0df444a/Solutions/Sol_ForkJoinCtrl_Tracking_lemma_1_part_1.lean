-- Prove2me | solution 1 for ForkJoinCtrl.Tracking.lemma_1_part_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T11:30:18.413989+00:00
-- url     : https://prove2.me/submissions/057c5e4e-96a1-4775-a062-66e74c5d42d3

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_LP

open ForkJoinCtrl.Tracking

theorem solution (N : Network) (b : LPParam N) (hb : b.Nonneg) (x : LPVar N)
    (hxf : LPFeasible N b x)
    (hxopt : IsLeast (LPObj N '' {x' | LPFeasible N b x'}) (LPObj N x)) :
    Feas17 N b x.q ∧ IsLeast (Obj17 N b '' {q | Feas17 N b q}) (Obj17 N b x.q) ∧
      Obj17 N b x.q = LPObj N x := by
  -- (A) every LP-feasible point has (17a)-value at most its (18a)-value
  have hA : ∀ x' : LPVar N, LPFeasible N b x' → Obj17 N b x'.q ≤ LPObj N x' := by
    intro x' hf
    unfold Obj17 LPObj
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (N.h_nonneg j)
    unfold Network.jobMax
    apply Finset.max'_le
    intro c hc
    rcases Finset.mem_union.1 hc with hc | hc
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hc
      have : N.own k = j := by simpa [Network.Kj] using hk
      rw [← this]; exact hf.1 k
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hc
      have : N.P i j = true := by simpa [Network.Ij] using hi
      have := hf.2.1 i j this
      linarith
  -- (B) every (17)-feasible q lifts to an LP-feasible point with equal value
  have hB : ∀ q, Feas17 N b q →
      LPFeasible N b ⟨fun j => N.jobMax j b.1 (fun i => q i j), q⟩ ∧
      LPObj N ⟨fun j => N.jobMax j b.1 (fun i => q i j), q⟩ = Obj17 N b q := by
    intro q hq
    refine ⟨⟨?_, ?_, hq.1, hq.2.1, hq.2.2⟩, rfl⟩
    · intro k
      unfold Network.jobMax
      apply Finset.le_max'
      apply Finset.mem_union_left
      exact Finset.mem_image.2 ⟨k, by simp [Network.Kj], rfl⟩
    · intro i j hij
      simp only [sub_nonneg]
      unfold Network.jobMax
      apply Finset.le_max'
      apply Finset.mem_union_right
      exact Finset.mem_image.2 ⟨i, by simp [Network.Ij, hij], rfl⟩
  have hfq : Feas17 N b x.q := ⟨hxf.2.2.1, hxf.2.2.2.1, hxf.2.2.2.2⟩
  have heq : Obj17 N b x.q = LPObj N x := by
    apply le_antisymm (hA x hxf)
    obtain ⟨h1, h2⟩ := hB x.q hfq
    rw [← h2]
    exact hxopt.2 ⟨_, h1, rfl⟩
  refine ⟨hfq, ⟨⟨x.q, hfq, rfl⟩, ?_⟩, heq⟩
  rintro v ⟨q, hq, rfl⟩
  obtain ⟨h1, h2⟩ := hB q hq
  rw [heq, ← h2]
  exact hxopt.2 ⟨_, h1, rfl⟩
