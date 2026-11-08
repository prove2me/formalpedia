-- Prove2me | solution 1 for FuchsThesis.Daroczy.eq_2_120
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:56:16.7782+00:00
-- url     : https://prove2.me/submissions/1e50b629-1596-4b2b-8eb1-8be1a91b63c0

import Mathlib
import Definitions.Def_FuchsThesis_Daroczy_IsDist
import Definitions.Def_FuchsThesis_Daroczy_IsSymmetric
import Definitions.Def_FuchsThesis_Daroczy_SatisfiesRecursion

open FuchsThesis.Daroczy in
theorem solution (α : ℝ) (hα : 0 < α) (hα1 : α ≠ 1) (H : (n : ℕ) → (Fin n → ℝ) → ℝ)
    (hsym : IsSymmetric H) (hrec : SatisfiesRecursion α H) :
    H 2 ![0, 1 - 0] = 0 ∧ H 2 ![1, 1 - 1] = 0 := by
  simp only [sub_zero, sub_self]
  have f02 : (0:Fin 3) ≠ 2 := by decide
  have f12 : (1:Fin 3) ≠ 2 := by decide
  have f20 : (2:Fin 3) ≠ 0 := by decide
  have f10 : (1:Fin 3) ≠ 0 := by decide
  obtain ⟨p, hp⟩ : ∃ p : Fin 3 → ℝ, p = fun i => if i = 2 then 0 else 1/2 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : Fin 3 → ℝ, q = fun i => if i = 0 then 0 else 1/2 := ⟨_, rfl⟩
  have hpd : IsDist p := by
    refine ⟨fun i => ?_, ?_⟩
    · simp only [hp]
      split_ifs <;> norm_num
    · rw [hp, Fin.sum_univ_three]; norm_num [f02, f12, f20, f10]
  have hqd : IsDist q := by
    refine ⟨fun i => ?_, ?_⟩
    · simp only [hq]
      split_ifs <;> norm_num
    · rw [hq, Fin.sum_univ_three]; norm_num [f02, f12, f20, f10]
  have hpq : p ∘ (Equiv.swap (0 : Fin 3) 2) = q := by
    funext i
    fin_cases i <;> simp [hp, hq, Equiv.swap_apply_def, f02, f12, f20, f10]
  have h3 : H 3 q = H 3 p := by
    rw [← hpq]
    exact hsym 3 _ p hpd
  have hr1 := hrec 1 p hpd (by norm_num [hp, f02, f12, f20, f10])
  have hr2 := hrec 1 q hqd (by simp [hq, f02, f12, f20, f10])
  have c1 : (Fin.cons (p 0 + p 1) (fun i : Fin 1 => p i.succ.succ) : Fin (1 + 1) → ℝ) =
      ![1, 0] := by
    funext i
    fin_cases i <;> norm_num [hp, f02, f12, f20, f10]
  have c2 : (![p 0 / (p 0 + p 1), p 1 / (p 0 + p 1)] : Fin 2 → ℝ) = ![1/2, 1/2] := by
    funext i
    fin_cases i <;> norm_num [hp, f02, f12, f20, f10]
  have c3 : (Fin.cons (q 0 + q 1) (fun i : Fin 1 => q i.succ.succ) : Fin (1 + 1) → ℝ) =
      ![1/2, 1/2] := by
    funext i
    fin_cases i <;> simp [hq, f02, f12, f20, f10]
  have c4 : (![q 0 / (q 0 + q 1), q 1 / (q 0 + q 1)] : Fin 2 → ℝ) = ![0, 1] := by
    funext i
    fin_cases i <;> simp [hq, f02, f12, f20, f10]
  have hs1 : p 0 + p 1 = 1 := by norm_num [hp, f02, f12, f20, f10]
  have hs2 : q 0 + q 1 = 1/2 := by simp [hq, f02, f12, f20, f10]
  rw [c1, c2, hs1, Real.one_rpow, one_mul] at hr1
  rw [c3, c4, hs2] at hr2
  have hswap : H 2 ![0, 1] = H 2 ![1, 0] := by
    have h := hsym 2 (Equiv.swap (0 : Fin 2) 1) ![1, 0] ⟨fun i => by fin_cases i <;> simp,
      by simp⟩
    have e : (![1, 0] : Fin 2 → ℝ) ∘ (Equiv.swap (0 : Fin 2) 1) = ![0, 1] := by
      funext i
      fin_cases i <;> simp [Equiv.swap_apply_def]
    rw [e] at h
    exact h
  have hlt : (1/2 : ℝ) ^ α < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have key : H 2 ![1, 0] = (1/2 : ℝ) ^ α * H 2 ![0, 1] := by
    have := h3
    rw [hr1, hr2] at this
    linarith
  rw [hswap] at key
  have hz : H 2 ![1, 0] = 0 := by
    have : (1 - (1/2 : ℝ) ^ α) * H 2 ![1, 0] = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact h
  exact ⟨by rw [hswap, hz], hz⟩
