-- Prove2me | solution 1 for FoundationsRL.RLBasics.performance_difference
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T13:48:10.79022+00:00
-- url     : https://prove2.me/submissions/e507e58d-7562-4492-9fd7-5d7c8c81fccc

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core

set_option autoImplicit false

open FoundationsRL.RLBasics in
theorem rl9529_V_succ {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (π : Policy S A H) (h : ℕ) (hh : h < H) (s : S) :
    V M π h s = ∑ a : A, π h s a * (M.R h s a + ∑ s' : S, M.P h s a s' * V M π (h + 1) s') := by
  unfold V
  obtain ⟨k, hk⟩ : ∃ k, H - h = k + 1 := ⟨H - h - 1, by omega⟩
  rw [hk, valueAux]
  have e1 : H - 1 - k = h := by omega
  have e2 : H - (h + 1) = k := by omega
  simp only [e1, e2]

open FoundationsRL.RLBasics in
theorem rl9529_V_H {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] {H : ℕ}
    (M : EpisodicMDP S A H) (π : Policy S A H) (s : S) : V M π H s = 0 := by
  unfold V
  simp [valueAux]

open FoundationsRL.RLBasics in
theorem rl9529_stateExp_succ {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S]
    {H : ℕ} (M : EpisodicMDP S A H) (π : Policy S A H) (s0 : S) (h : ℕ) (g : S → ℝ) :
    stateExp M π s0 h (fun sh => ∑ a : A, π h sh a * ∑ s' : S, M.P h sh a s' * g s') =
      stateExp M π s0 (h + 1) g := by
  unfold stateExp
  simp only [stateDist]
  have hR : ∀ s' : S, (∑ sp : S, stateDist M π s0 h sp * ∑ a : A, π h sp a * M.P h sp a s') * g s' =
      ∑ sp : S, ∑ a : A, stateDist M π s0 h sp * (π h sp a * (M.P h sp a s' * g s')) := by
    intro s'
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun sp _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    ring
  have hL : ∀ sh : S, stateDist M π s0 h sh * ∑ a : A, π h sh a * ∑ s' : S, M.P h sh a s' * g s' =
      ∑ a : A, ∑ s' : S, stateDist M π s0 h sh * (π h sh a * (M.P h sh a s' * g s')) := by
    intro sh
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
  simp only [hR, hL]
  rw [Finset.sum_comm (f := fun (s' : S) (sp : S) =>
    ∑ a : A, stateDist M π s0 h sp * (π h sp a * (M.P h sp a s' * g s')))]
  refine Finset.sum_congr rfl (fun sp _ => ?_)
  rw [Finset.sum_comm]

open FoundationsRL.RLBasics in
theorem rl9529_telescope {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S]
    {H : ℕ} (M : EpisodicMDP S A H) (π : Policy S A H) (s0 : S)
    (f g : ℕ → S → ℝ) (hH : ∀ s, f H s = 0)
    (hstep : ∀ h, h < H → ∀ sh, f h sh =
      g h sh + ∑ a : A, π h sh a * ∑ s' : S, M.P h sh a s' * f (h + 1) s') :
    f 0 s0 = ∑ h ∈ Finset.range H, stateExp M π s0 h (g h) := by
  have key : ∀ k, k ≤ H → f 0 s0 =
      ∑ h ∈ Finset.range k, stateExp M π s0 h (g h) + stateExp M π s0 k (f k) := by
    intro k hk
    induction k with
    | zero =>
      simp [stateExp, stateDist]
    | succ k ih =>
      rw [ih (by omega), Finset.sum_range_succ, ← rl9529_stateExp_succ]
      have hsplit : stateExp M π s0 k (f k) = stateExp M π s0 k (g k) +
          stateExp M π s0 k (fun sh => ∑ a : A, π k sh a * ∑ s' : S, M.P k sh a s' * f (k + 1) s') := by
        unfold stateExp
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun sh _ => ?_)
        rw [hstep k (by omega) sh]
        ring
      rw [hsplit]
      ring
  rw [key H le_rfl]
  simp [stateExp, hH]

open FoundationsRL.RLBasics in
theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    [DecidableEq S] [DecidableEq A] {H : ℕ} (M : EpisodicMDP S A H) (π π' : Policy S A H)
    (hπ : IsPolicy H π) (hπ' : IsPolicy H π') (s : S) :
    V M π' 0 s - V M π 0 s =
      ∑ h ∈ Finset.range H,
        stateExp M π s h (fun sh =>
          (∑ a' : A, π' h sh a' * Q M π' h sh a') -
            ∑ a : A, π h sh a * Q M π' h sh a) := by
  refine rl9529_telescope M π s (fun h x => V M π' h x - V M π h x)
    (fun h sh => (∑ a' : A, π' h sh a' * Q M π' h sh a') - ∑ a : A, π h sh a * Q M π' h sh a)
    (fun x => by simp [rl9529_V_H]) ?_
  intro h hh sh
  simp only [Q, if_pos hh]
  rw [rl9529_V_succ M π' h hh sh, rl9529_V_succ M π h hh sh]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  ring
