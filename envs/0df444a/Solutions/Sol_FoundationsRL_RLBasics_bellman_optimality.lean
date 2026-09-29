-- Prove2me | solution 1 for FoundationsRL.RLBasics.bellman_optimality
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T05:26:12.659856+00:00
-- url     : https://prove2.me/submissions/9cb2aa13-41c7-4645-bcb1-d1146851398b

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core



namespace FoundationsRL.RLBasics

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
  {H : ℕ}

lemma bo_V_succ (M : EpisodicMDP S A H) (π : Policy S A H) (h : ℕ) (hh : h < H) (s : S) :
    V M π h s = ∑ a, π h s a * (M.R h s a + ∑ s', M.P h s a s' * V M π (h + 1) s') := by
  unfold V
  obtain ⟨k, hk⟩ : ∃ k, H - h = k + 1 := ⟨H - h - 1, by omega⟩
  have h1 : H - 1 - k = h := by omega
  have h2 : H - (h + 1) = k := by omega
  rw [hk, h2]
  simp only [valueAux, h1]

lemma bo_V_top (M : EpisodicMDP S A H) (π : Policy S A H) (s : S) : V M π H s = 0 := by
  simp [V, valueAux]

lemma bo_Q (M : EpisodicMDP S A H) (π : Policy S A H) (h : ℕ) (hh : h < H) (s : S) (a : A) :
    Q M π h s a = M.R h s a + ∑ s', M.P h s a s' * V M π (h + 1) s' := by
  simp [Q, hh]

lemma bo_det_valid (πdet : ℕ → S → A) : IsPolicy H (detPolicy (H := H) πdet) := by
  intro h _ s
  refine ⟨fun a => ?_, ?_⟩
  · simp only [detPolicy]; split_ifs <;> norm_num
  · simp [detPolicy]

lemma bo_V_det (M : EpisodicMDP S A H) (πdet : ℕ → S → A) (h : ℕ) (hh : h < H) (s : S) :
    V M (detPolicy πdet) h s = M.R h s (πdet h s)
      + ∑ s', M.P h s (πdet h s) s' * V M (detPolicy πdet) (h + 1) s' := by
  rw [bo_V_succ M _ h hh s]
  simp [detPolicy, ite_mul]

theorem bo_main (M : EpisodicMDP S A H) :
    ∃ πdet : ℕ → S → A,
      (∀ h, h < H → ∀ s : S, IsArgmax (Qstar M h s) (πdet h s)) ∧
      (∀ h, h < H → ∀ s : S, ∀ a : A, Qstar M h s a = bellmanOp M h (Qstar M (h + 1)) s a) ∧
      (∀ h, h ≤ H → ∀ s : S, V M (detPolicy πdet) h s = Vstar M h s) := by
  have hex : ∀ h s, ∃ a, ∀ a', Qstar M h s a' ≤ Qstar M h s a := fun h s => Finite.exists_max _
  choose πdet hπdet using hex
  have hvalid : IsPolicy H (detPolicy (H := H) πdet) := bo_det_valid πdet
  haveI : Nonempty {π : Policy S A H // IsPolicy H π} := ⟨⟨_, hvalid⟩⟩
  have hQtop : ∀ s a, Qstar M H s a = 0 := by
    intro s a
    unfold Qstar
    simp only [Q, lt_irrefl, if_false]
    exact ciSup_const
  have hVstar_max : ∀ h s, Vstar M h s = Qstar M h s (πdet h s) := by
    intro h s
    unfold Vstar
    exact le_antisymm (ciSup_le (hπdet h s)) (le_ciSup (Set.finite_range _).bddAbove _)
  -- one step of backward induction for `Qstar`
  have hQgen : ∀ h, h < H → (∀ s, V M (detPolicy πdet) (h + 1) s = Vstar M (h + 1) s) →
      (∀ π : Policy S A H, IsPolicy H π → ∀ s, V M π (h + 1) s ≤ Vstar M (h + 1) s) →
      ∀ s a, Qstar M h s a = M.R h s a + ∑ s', M.P h s a s' * Vstar M (h + 1) s' := by
    intro h hlt ihdet ihall s a
    have hbound : ∀ π : Policy S A H, IsPolicy H π →
        Q M π h s a ≤ M.R h s a + ∑ s', M.P h s a s' * Vstar M (h + 1) s' := by
      intro π hπ
      rw [bo_Q M π h hlt]
      exact add_le_add le_rfl (Finset.sum_le_sum fun s' _ =>
        mul_le_mul_of_nonneg_left (ihall π hπ s') (M.P_nonneg _ _ _ _))
    unfold Qstar
    apply le_antisymm
    · exact ciSup_le fun π => hbound π.1 π.2
    · refine le_ciSup_of_le ?_ ⟨_, hvalid⟩ ?_
      · refine ⟨M.R h s a + ∑ s', M.P h s a s' * Vstar M (h + 1) s', ?_⟩
        rintro _ ⟨π, rfl⟩
        exact hbound π.1 π.2
      · rw [bo_Q M _ h hlt]
        simp only [ihdet]
        exact le_rfl
  have key : ∀ k, k ≤ H → (∀ s, V M (detPolicy πdet) (H - k) s = Vstar M (H - k) s) ∧
      (∀ π : Policy S A H, IsPolicy H π → ∀ s, V M π (H - k) s ≤ Vstar M (H - k) s) := by
    intro k
    induction k with
    | zero =>
      intro _
      have hV0 : ∀ s, Vstar M H s = 0 := by
        intro s
        rw [hVstar_max, hQtop]
      simp only [Nat.sub_zero]
      exact ⟨fun s => by rw [bo_V_top, hV0], fun π _ s => by rw [bo_V_top, hV0]⟩
    | succ k ih =>
      intro hk
      obtain ⟨ihdet, ihall⟩ := ih (by omega)
      have hlt : H - (k + 1) < H := by omega
      have hh1 : H - (k + 1) + 1 = H - k := by omega
      rw [← hh1] at ihdet ihall
      have hQ := hQgen (H - (k + 1)) hlt ihdet ihall
      constructor
      · intro s
        rw [bo_V_det M πdet _ hlt s, hVstar_max _ s, hQ s (πdet _ s)]
        simp only [ihdet]
      · intro π hπ s
        rw [bo_V_succ M π _ hlt s]
        obtain ⟨hπnn, hπsum⟩ := hπ _ hlt s
        calc ∑ a, π (H - (k + 1)) s a * (M.R (H - (k + 1)) s a
              + ∑ s', M.P (H - (k + 1)) s a s' * V M π (H - (k + 1) + 1) s')
            ≤ ∑ a, π (H - (k + 1)) s a * Qstar M (H - (k + 1)) s a := by
              refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ (hπnn a)
              rw [hQ s a]
              exact add_le_add le_rfl (Finset.sum_le_sum fun s' _ =>
                mul_le_mul_of_nonneg_left (ihall π hπ s') (M.P_nonneg _ _ _ _))
          _ ≤ ∑ a, π (H - (k + 1)) s a * Vstar M (H - (k + 1)) s := by
              refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ (hπnn a)
              exact le_ciSup (Set.finite_range _).bddAbove a
          _ = Vstar M (H - (k + 1)) s := by rw [← Finset.sum_mul, hπsum, one_mul]
  refine ⟨πdet, fun h _ s => hπdet h s, ?_, ?_⟩
  · intro h hh s a
    obtain ⟨kd, ka⟩ := key (H - (h + 1)) (by omega)
    rw [show H - (H - (h + 1)) = h + 1 by omega] at kd ka
    rw [hQgen h hh kd ka s a]
    rfl
  · intro h hh s
    have := (key (H - h) (by omega)).1 s
    rwa [show H - (H - h) = h by omega] at this

end FoundationsRL.RLBasics

open FoundationsRL.RLBasics

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S]
    [DecidableEq A] {H : ℕ} (M : EpisodicMDP S A H) :
    ∃ πdet : ℕ → S → A,
      (∀ h, h < H → ∀ s : S, IsArgmax (Qstar M h s) (πdet h s)) ∧
      (∀ h, h < H → ∀ s : S, ∀ a : A, Qstar M h s a = bellmanOp M h (Qstar M (h + 1)) s a) ∧
      (∀ h, h ≤ H → ∀ s : S, V M (detPolicy πdet) h s = Vstar M h s) := by
  exact bo_main M
