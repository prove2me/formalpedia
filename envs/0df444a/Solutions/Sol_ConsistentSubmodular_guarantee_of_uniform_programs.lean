-- Prove2me | solution 1 for ConsistentSubmodular.guarantee_of_uniform_programs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:37:27.564198+00:00
-- url     : https://prove2.me/submissions/708e3877-5877-4502-86d1-8a85132db66a

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_UniformTransfer
import Theorems.Thm_ConsistentSubmodular_ProtectedPrograms_trajectory_spec

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {n : ℕ}

theorem recourse_le_card_add (A B : Finset (Fin n)) :
    recourse A B ≤ A.card + B.card := by
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add (Finset.card_le_card Finset.sdiff_subset)
      (Finset.card_le_card Finset.sdiff_subset))

theorem recourse_le_twice_budget {A B : Finset (Fin n)} {k : ℕ}
    (hA : A.card ≤ k) (hB : B.card ≤ k) : recourse A B ≤ 2 * k := by
  have := recourse_le_card_add A B
  omega

namespace Objective

variable (f : Objective n)

theorem exactTrajectory_feasible (k : ℕ) :
    FeasibleTrajectory k (2 * k) (f.exactTrajectory k) := by
  have hspec : ∀ t : Fin (n + 1),
      f.exactTrajectory k t ⊆ arrivedPrefix n t.val ∧
      (f.exactTrajectory k t).card ≤ k := by
    intro t
    exact ⟨(f.bufferedOptimizer_spec _ _ _).1,
      (f.bufferedOptimizer_spec _ _ _).2.1⟩
  refine ⟨?_, hspec, ?_⟩
  · exact Finset.subset_empty.mp (by simpa using (hspec 0).1)
  · intro t
    exact recourse_le_twice_budget (hspec t.succ).2 (hspec t.castSucc).2

theorem exactTrajectory_optimal (k : ℕ) (t : Fin (n + 1))
    (A : Finset (Fin n)) (hA : A ⊆ arrivedPrefix n t.val) (hk : A.card ≤ k) :
    f.value A ≤ f.value (f.exactTrajectory k t) := by
  simpa [exactTrajectory] using
    (f.bufferedOptimizer_spec (arrivedPrefix n t.val) ∅ k).2.2 A hA hk

theorem exists_exact_trajectory (k : ℕ) :
    ∃ S : Fin (n + 1) → Finset (Fin n),
      FeasibleTrajectory k (2 * k) S ∧
      ∀ (t : Fin (n + 1)) (A : Finset (Fin n)),
        A ⊆ arrivedPrefix n t.val → A.card ≤ k → f.value A ≤ f.value (S t) :=
  ⟨f.exactTrajectory k, f.exactTrajectory_feasible k, f.exactTrajectory_optimal k⟩

end Objective

/-- The small-capacity branch has a uniform bound once `K` is fixed. -/
theorem small_budget_trajectory (K k : ℕ) (hk : k ≤ K)
    (f : Objective n) {α : ℝ} (hα : α ≤ 1) :
    ∃ S : Fin (n + 1) → Finset (Fin n), FeasibleTrajectory k (2 * K) S ∧
      ∀ (t : Fin (n + 1)) (A : Finset (Fin n)),
        A ⊆ arrivedPrefix n t.val → A.card ≤ k → α * f.value A ≤ f.value (S t) := by
  obtain ⟨S, hS, hopt⟩ := f.exists_exact_trajectory k
  refine ⟨S, ⟨hS.1, hS.2.1, ?_⟩, ?_⟩
  · intro t
    exact (hS.2.2 t).trans (Nat.mul_le_mul_left 2 hk)
  · intro t A hA hAk
    exact (mul_le_of_le_one_left (f.nonnegative A) hα).trans (hopt t A hA hAk)

end ConsistentSubmodular

end

end

section

noncomputable section

namespace ConsistentSubmodular

/-- A level at most the slack needs no recourse: the empty trajectory meets it. -/
theorem consistentGuarantee_of_le_slack {α ε : ℝ} (h : α ≤ ε) (R : ℕ) :
    ConsistentGuarantee α ε R := by
  intro n k f
  refine ⟨fun _ => ∅, ⟨rfl, fun _ => ⟨Finset.empty_subset _, by simp⟩,
    fun _ => by simp [recourse]⟩, ?_⟩
  intro t A _ _
  have hA := f.nonnegative A
  have h0 := f.nonnegative ∅
  nlinarith

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular

theorem solution {α ε : ℝ} {N H R : ℕ} (hN : 200 ≤ N)
    (hα : α ≤ 3 / 4) (hNε : 20 * ((1 : ℝ) / N) < ε)
    (hprograms : HasUniformPrograms α N H R) :
    ConsistentGuarantee α ε (2 * transferThreshold N H + R + 2) := by
  by_cases hαε : α ≤ ε
  · exact consistentGuarantee_of_le_slack hαε _
  intro n k f
  have hη0 : 0 ≤ (1 : ℝ) / N := by positivity
  have hγ : 0 ≤ α - 14 * ((1 : ℝ) / N) := by linarith
  let K := transferThreshold N H
  by_cases hk : k ≤ K
  · obtain ⟨S, hS, hval⟩ := small_budget_trajectory K k hk f
      (show α - ε ≤ 1 by linarith)
    refine ⟨S, ⟨hS.1, hS.2.1, ?_⟩, hval⟩
    intro t
    exact (hS.2.2 t).trans (by omega)
  · have hklarge : transferThreshold N H ≤ k := by dsimp [K] at hk; omega
    let p := transferParameters N H k hN hklarge
    obtain ⟨P⟩ := hprograms n k f p
    have hkp : 0 < k := by omega
    obtain ⟨hfeas, hval⟩ := P.trajectory_spec p hkp hα hγ
    refine ⟨(fun t => P.selected t.val), ⟨hfeas.1, hfeas.2.1, ?_⟩, ?_⟩
    · intro t
      exact (hfeas.2.2 t).trans (by omega)
    · intro t A hA hAk
      have hcoef : α - ε ≤ α - 14 * ((1 : ℝ) / N) := by linarith
      exact (mul_le_mul_of_nonneg_right hcoef (f.nonnegative A)).trans (hval t A hA hAk)

end
