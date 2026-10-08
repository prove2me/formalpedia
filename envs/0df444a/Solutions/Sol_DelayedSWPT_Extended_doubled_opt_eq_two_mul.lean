-- Prove2me | solution 1 for DelayedSWPT.Extended.doubled_opt_eq_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T12:10:52.345364+00:00
-- url     : https://prove2.me/submissions/8ed551f4-1238-4058-8d68-3af131856eb1

import Mathlib
import Definitions.Def_DelayedSWPT_Extended_Problem

open DelayedSWPT.Model DelayedSWPT.Extended in
theorem solution {n : ℕ} (I : Instance n) (πstar μstar : Fin n → ℕ)
    (hπ : IsOptimal I.r I.p I.w πstar)
    (hμ : IsOptimal (double I).r (double I).p (double I).w μstar) :
    cost (double I).w (double I).p μstar = 2 * cost I.w I.p πstar := by
  have hr2 : ∀ j, (double I).r j = 2 * I.r j := fun _ => rfl
  have hp2 : ∀ j, (double I).p j = 2 * I.p j := fun _ => rfl
  have hw2 : (double I).w = I.w := rfl
  -- upper bound: doubling πstar is feasible for (2P)
  have hfeas1 : IsFeasible (double I).r (double I).p (fun j => 2 * πstar j) := by
    obtain ⟨h1, h2⟩ := hπ.1
    refine ⟨fun j => ?_, fun i j hij => ?_⟩ <;> dsimp only
    · rw [hr2]; have := h1 j; omega
    · rw [hp2, hp2]; rcases h2 i j hij with h | h
      · left; omega
      · right; omega
  have hup : cost (double I).w (double I).p μstar ≤ 2 * cost I.w I.p πstar := by
    have := hμ.2 _ hfeas1
    refine this.trans (le_of_eq ?_)
    unfold cost
    rw [hw2, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hp2]
    push_cast
    ring
  -- lower bound: halving μstar is feasible for (P)
  have hfeas2 : IsFeasible I.r I.p (fun j => μstar j / 2) := by
    obtain ⟨h1, h2⟩ := hμ.1
    refine ⟨fun j => ?_, fun i j hij => ?_⟩ <;> dsimp only
    · have := h1 j; rw [hr2] at this; omega
    · have := h2 i j hij; rw [hp2, hp2] at this; rcases this with h | h
      · left; omega
      · right; omega
  have hlow : 2 * cost I.w I.p πstar ≤ cost (double I).w (double I).p μstar := by
    have h := hπ.2 _ hfeas2
    have h' : 2 * cost I.w I.p (fun j => μstar j / 2) ≤ cost (double I).w (double I).p μstar := by
      unfold cost
      rw [hw2, Finset.mul_sum]
      refine Finset.sum_le_sum (fun j _ => ?_)
      have hw := (I.w_pos j).le
      have hle : 2 * ((μstar j / 2 + I.p j : ℕ) : ℝ) ≤ ((μstar j + (double I).p j : ℕ) : ℝ) := by
        rw [hp2]
        have : 2 * (μstar j / 2 + I.p j) ≤ μstar j + 2 * I.p j := by omega
        exact_mod_cast this
      nlinarith
    linarith
  exact le_antisymm hup hlow
