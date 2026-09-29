-- Prove2me | solution 1 for CompetitivePaging.Combining.exists_sequence_forcing_moves
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T05:09:50.539524+00:00
-- url     : https://prove2.me/submissions/c57517cf-effd-4783-9eaf-1a86c11e3c9d

import Mathlib
import Definitions.Def_KServer_model



namespace CompetitivePaging.Combining

theorem moveCost_ge_one_of_ne {k : ℕ} {M : Type} [MetricSpace M]
    (hM : ∀ x y : M, x ≠ y → dist x y = 1) (C D : KServer.Config k M) (h : C ≠ D) :
    1 ≤ KServer.moveCost C D := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 h
  unfold KServer.moveCost
  calc (1 : ℝ) = dist (C j) (D j) := (hM _ _ hj).symm
    _ ≤ ∑ i, dist (C i) (D i) :=
      Finset.single_le_sum (f := fun i => dist (C i) (D i)) (fun i _ => dist_nonneg) (Finset.mem_univ j)

theorem forcing_core {m : ℕ} (hm : 0 < m) {M : Type} [MetricSpace M]
    (hM : ∀ x y : M, x ≠ y → dist x y = 1) (e : Fin m × Fin 2 ≃ M)
    (A : KServer.OnlineAlgorithm (2 * m - 1) M) (N : ℕ) :
    ∃ τ : List M, τ.length = N ∧
      (∀ j < N, A.conf (τ.take j) ≠ A.conf (τ.take (j + 1))) ∧
      (N : ℝ) ≤ A.cost τ := by
  classical
  have hne : ∀ C : Fin (2 * m - 1) → M, ∃ x, ∀ j, C j ≠ x := by
    intro C
    by_contra h
    push_neg at h
    have hs : Function.Surjective (e.symm ∘ C) := by
      intro p
      obtain ⟨j, hj⟩ := h (e p)
      exact ⟨j, by simp [hj]⟩
    have := Fintype.card_le_of_surjective _ hs
    simp at this
    omega
  choose u hu using hne
  let f : ℕ → List M := fun n => Nat.rec [] (fun _ l => l ++ [u (A.conf l)]) n
  have hf0 : f 0 = [] := rfl
  have hfs : ∀ n, f (n + 1) = f n ++ [u (A.conf (f n))] := fun n => rfl
  have hlen : ∀ n, (f n).length = n := by
    intro n; induction n with
    | zero => simp [hf0]
    | succ n ih => simp [hfs, ih]
  have htake : ∀ n j, j ≤ n → (f n).take j = f j := by
    intro n; induction n with
    | zero => intro j hj; simp at hj; subst hj; simp [hf0]
    | succ n ih =>
      intro j hj
      rcases Nat.lt_or_ge j (n + 1) with h | h
      · rw [hfs, List.take_append_of_le_length (by rw [hlen]; omega)]
        exact ih j (by omega)
      · have : j = n + 1 := by omega
        subst this
        exact List.take_of_length_le (hlen (n + 1)).le
  have hmove : ∀ j < N, A.conf ((f N).take j) ≠ A.conf ((f N).take (j + 1)) := by
    intro j hj
    rw [htake N j hj.le, htake N (j + 1) hj, hfs]
    intro heq
    obtain ⟨s, hs⟩ := A.serves (f j) (u (A.conf (f j)))
    rw [← heq] at hs
    exact hu _ s hs
  refine ⟨f N, hlen N, hmove, ?_⟩
  unfold KServer.OnlineAlgorithm.cost
  rw [hlen]
  calc (N : ℝ) = ∑ j ∈ Finset.range N, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun j hj =>
        moveCost_ge_one_of_ne hM _ _ (hmove j (Finset.mem_range.1 hj))

end CompetitivePaging.Combining

open CompetitivePaging.Combining


theorem solution {m : ℕ} (hm : 0 < m) {M : Type} [MetricSpace M]
    (hM : ∀ x y : M, x ≠ y → dist x y = 1) (e : Fin m × Fin 2 ≃ M)
    (A : KServer.OnlineAlgorithm (2 * m - 1) M) (N : ℕ) :
    ∃ τ : List M, τ.length = N ∧
      (∀ j < N, A.conf (τ.take j) ≠ A.conf (τ.take (j + 1))) ∧
      (N : ℝ) ≤ A.cost τ := by
  exact forcing_core hm hM e A N
