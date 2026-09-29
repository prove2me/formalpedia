-- Prove2me | solution 1 for FoundationsRL.RLBasics.error_decomposition_optimistic
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T05:29:14.314331+00:00
-- url     : https://prove2.me/submissions/510aaa2e-74cb-49ee-b220-10a5189e825c

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

theorem ed_main (M : EpisodicMDP S A H) (Qhat : ℕ → S → A → ℝ)
    (hterm : ∀ s a, Qhat H s a = 0) (hopt : ∀ h, h < H → ∀ s a, Qstar M h s a ≤ Qhat h s a)
    (πdet : ℕ → S → A) (hgreedy : ∀ h, h < H → ∀ s : S, IsArgmax (Qhat h s) (πdet h s))
    (s : S) :
    Vstar M 0 s - V M (detPolicy πdet) 0 s ≤
      ∑ h ∈ Finset.range H,
        stateExp M (detPolicy πdet) s h (fun sh =>
          Qhat h sh (πdet h sh) - bellmanOp M h (Qhat (h + 1)) sh (πdet h sh)) := by
  set U : ℕ → S → ℝ := fun h s => Qhat h s (πdet h s) with hU
  set W : ℕ → S → ℝ := fun h s => V M (detPolicy πdet) h s with hW
  set δ : ℕ → S → ℝ := fun h sh =>
    Qhat h sh (πdet h sh) - bellmanOp M h (Qhat (h + 1)) sh (πdet h sh) with hδ
  have hvalid : IsPolicy H (detPolicy (H := H) πdet) := bo_det_valid πdet
  haveI : Nonempty {π : Policy S A H // IsPolicy H π} := ⟨⟨_, hvalid⟩⟩
  have hsupU : ∀ h, h < H → ∀ s', (⨆ a', Qhat (h + 1) s' a') = U (h + 1) s' := by
    intro h hh s'
    rcases Nat.lt_or_ge (h + 1) H with h1 | h1
    · exact le_antisymm (ciSup_le (hgreedy (h + 1) h1 s'))
        (le_ciSup (f := fun a' => Qhat (h + 1) s' a') (Set.finite_range _).bddAbove
          (πdet (h + 1) s'))
    · have hH : h + 1 = H := by omega
      simp only [hU, hH, hterm]
      exact ciSup_const
  have hstep : ∀ h, h < H → ∀ s', U h s' - W h s' =
      δ h s' + ∑ s'', M.P h s' (πdet h s') s'' * (U (h + 1) s'' - W (h + 1) s'') := by
    intro h hh s'
    have hb : bellmanOp M h (Qhat (h + 1)) s' (πdet h s') =
        M.R h s' (πdet h s') + ∑ s'', M.P h s' (πdet h s') s'' * U (h + 1) s'' := by
      simp only [bellmanOp, hsupU h hh]
    simp only [hW, hδ, hU] at hb ⊢
    rw [bo_V_det M πdet h hh s', hb]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have hdist : ∀ h (g : S → ℝ), stateExp M (detPolicy πdet) s (h + 1) g =
      ∑ sp, stateDist M (detPolicy πdet) s h sp * ∑ s', M.P h sp (πdet h sp) s' * g s' := by
    intro h g
    have e : ∀ sp s', ∑ a, detPolicy (H := H) πdet h sp a * M.P h sp a s' = M.P h sp (πdet h sp) s' := by
      intro sp s'
      simp [detPolicy, ite_mul]
    simp only [stateExp, stateDist, e, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  have hexp_sub : ∀ h (f g : S → ℝ), stateExp M (detPolicy πdet) s h (fun x => f x + g x) =
      stateExp M (detPolicy πdet) s h f + stateExp M (detPolicy πdet) s h g := by
    intro h f g
    simp only [stateExp, mul_add, Finset.sum_add_distrib]
  have htele : ∀ n, n ≤ H → U 0 s - W 0 s = ∑ h ∈ Finset.range n, stateExp M (detPolicy πdet) s h (δ h)
      + stateExp M (detPolicy πdet) s n (fun x => U n x - W n x) := by
    intro n
    induction n with
    | zero =>
      intro _
      simp [stateExp, stateDist]
    | succ n ih =>
      intro hn
      have hlt : n < H := by omega
      rw [ih (by omega), Finset.sum_range_succ, add_assoc]
      congr 1
      have e1 : (fun x => U n x - W n x) = fun x => δ n x +
          ∑ s'', M.P n x (πdet n x) s'' * (U (n + 1) s'' - W (n + 1) s'') :=
        funext fun x => hstep n hlt x
      rw [e1, hexp_sub, hdist]
      rfl
  have hfin : stateExp M (detPolicy πdet) s H (fun x => U H x - W H x) = 0 := by
    simp [stateExp, hU, hW, hterm, bo_V_top]
  have hVU : Vstar M 0 s ≤ U 0 s := by
    rcases Nat.eq_zero_or_pos H with hH | hH
    · have hQ0 : ∀ a, Qstar M 0 s a = 0 := by
        intro a
        unfold Qstar
        simp only [Q, hH, lt_irrefl, if_false]
        exact ciSup_const
      have hU0 : U 0 s = 0 := by simp only [hU]; rw [hH] at hterm; exact hterm s _
      unfold Vstar
      simp only [hQ0, ciSup_const, hU0, le_refl]
    · unfold Vstar
      exact ciSup_le fun a => (hopt 0 hH s a).trans (hgreedy 0 hH s a)
  have h := htele H le_rfl
  rw [hfin, add_zero] at h
  calc Vstar M 0 s - V M (detPolicy πdet) 0 s ≤ U 0 s - W 0 s := by
        simp only [hW]; linarith
    _ = _ := h

end FoundationsRL.RLBasics

open FoundationsRL.RLBasics

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    [DecidableEq S] [DecidableEq A] {H : ℕ} (M : EpisodicMDP S A H) (Qhat : ℕ → S → A → ℝ)
    (hterm : ∀ s a, Qhat H s a = 0) (hopt : ∀ h, h < H → ∀ s a, Qstar M h s a ≤ Qhat h s a)
    (πdet : ℕ → S → A) (hgreedy : ∀ h, h < H → ∀ s : S, IsArgmax (Qhat h s) (πdet h s))
    (s : S) :
    Vstar M 0 s - V M (detPolicy πdet) 0 s ≤
      ∑ h ∈ Finset.range H,
        stateExp M (detPolicy πdet) s h (fun sh =>
          Qhat h sh (πdet h sh) - bellmanOp M h (Qhat (h + 1)) sh (πdet h sh)) := by
  exact ed_main M Qhat hterm hopt πdet hgreedy s
