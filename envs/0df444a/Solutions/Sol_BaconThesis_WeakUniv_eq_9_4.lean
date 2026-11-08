-- Prove2me | solution 1 for BaconThesis.WeakUniv.eq_9_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:19:37.796022+00:00
-- url     : https://prove2.me/submissions/d6c70889-8e0e-4531-86ca-c31adbb1fc75

import Definitions.Def_BaconThesis_WeakUniv_Tmat
import Definitions.Def_BaconThesis_WeakUniv_embed
import Definitions.Def_BaconThesis_WeakUniv_Sz

namespace Aux_Bacon_94
open BaconThesis.WeakUniv

def s (t : Fin 2) : ℂ := (-1 : ℂ) ^ (t : ℕ)

theorem sum_diff {n : ℕ} (k l : Fin n) (hkl : k ≠ l) (x y : Fin n → Fin 2)
    (hxy : ∀ m, m ≠ k → m ≠ l → x m = y m) :
    (∑ m, (-1 : ℂ) ^ (x m : ℕ)) - ∑ m, (-1 : ℂ) ^ (y m : ℕ) =
      s (x k) + s (x l) - s (y k) - s (y l) := by
  rw [← Finset.sum_sub_distrib, Fintype.sum_eq_add k l hkl]
  · unfold s; ring
  · intro m hm
    rw [hxy m hm.1 hm.2, sub_self]

theorem comm_iff {n : ℕ} (E : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
    Commute (Sz n) E ↔ ∀ x y, ((1 / 2 : ℂ) * ∑ m, (-1 : ℂ) ^ (x m : ℕ)) * E x y =
      E x y * ((1 / 2 : ℂ) * ∑ m, (-1 : ℂ) ^ (y m : ℕ)) := by
  unfold Commute SemiconjBy Sz
  constructor
  · intro h x y
    have := congrFun (congrFun h x) y
    rwa [Matrix.diagonal_mul, Matrix.mul_diagonal] at this
  · intro h
    ext x y
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    exact h x y

def pt {n : ℕ} (k l : Fin n) (a b : Fin 2) : Fin n → Fin 2 :=
  Function.update (Function.update (fun _ => 0) k a) l b

theorem pt_k {n : ℕ} (k l : Fin n) (hkl : k ≠ l) (a b : Fin 2) : pt k l a b k = a := by
  simp [pt, Function.update_of_ne hkl]
theorem pt_l {n : ℕ} (k l : Fin n) (a b : Fin 2) : pt k l a b l = b := by
  simp [pt]
theorem pt_o {n : ℕ} (k l : Fin n) (a b : Fin 2) (m : Fin n) (hk : m ≠ k) (hl : m ≠ l) :
    pt k l a b m = 0 := by
  simp [pt, Function.update_of_ne hk, Function.update_of_ne hl]

theorem key {n : ℕ} (k l : Fin n) (hkl : k ≠ l) (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hc : Commute (Sz n) (embed n k l M)) (a b c e : Fin 2) :
    (s a + s b - s c - s e) * M (a, b) (c, e) = 0 := by
  have h := (comm_iff _).mp hc (pt k l a b) (pt k l c e)
  have hag : ∀ m, m ≠ k → m ≠ l → pt k l a b m = pt k l c e m := by
    intro m h1 h2; rw [pt_o k l a b m h1 h2, pt_o k l c e m h1 h2]
  unfold embed at h
  rw [if_pos hag, pt_k k l hkl, pt_k k l hkl, pt_l, pt_l] at h
  have hd := sum_diff k l hkl _ _ hag
  rw [pt_k k l hkl, pt_k k l hkl, pt_l, pt_l] at hd
  have : ((1 / 2 : ℂ) * ((∑ m, (-1 : ℂ) ^ (pt k l a b m : ℕ)) - ∑ m, (-1 : ℂ) ^ (pt k l c e m : ℕ))) *
      M (a, b) (c, e) = 0 := by linear_combination h
  rw [hd] at this
  have h2 : (1 / 2 : ℂ) ≠ 0 := by norm_num
  have := this
  rw [mul_assoc] at this
  exact (mul_eq_zero.mp this).resolve_left h2

end Aux_Bacon_94

open BaconThesis.WeakUniv Aux_Bacon_94 in
theorem solution {n : ℕ} (k l : Fin n) (hkl : k ≠ l)
    (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hM : M.IsHermitian) :
    Commute (Sz n) (embed n k l M) ↔
      ∃ z₁ z₂ z₃ z₄ : ℝ, ∃ h : ℂ, M = Tmat z₁ z₂ z₃ z₄ h := by
  have hdiag : ∀ i, M i i = ((M i i).re : ℂ) := by
    intro i
    have := hM.apply i i
    exact (Complex.conj_eq_iff_re.mp this).symm
  constructor
  · intro hc
    have K := key k l hkl M hc
    refine ⟨(M (0, 0) (0, 0)).re, (M (0, 1) (0, 1)).re, (M (1, 0) (1, 0)).re,
      (M (1, 1) (1, 1)).re, M (0, 1) (1, 0), ?_⟩
    have h10 : M (1, 0) (0, 1) = star (M (0, 1) (1, 0)) := (hM.apply (1, 0) (0, 1)).symm
    have Kz : ∀ a b c e : Fin 2, s a + s b - s c - s e ≠ 0 → M (a, b) (c, e) = 0 :=
      fun a b c e h => (mul_eq_zero.mp (K a b c e)).resolve_left h
    ext ⟨a, b⟩ ⟨c, e⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
      simp [Tmat, finProdFinEquiv] <;>
      first
        | exact hdiag _
        | exact h10
        | (apply Kz; norm_num [s]; done)
        | (apply Kz; simp [s]; done)
        | (apply Kz; simp [s]; norm_num)
  · rintro ⟨z₁, z₂, z₃, z₄, h, rfl⟩
    rw [comm_iff]
    intro x y
    unfold embed
    by_cases hag : ∀ m, m ≠ k → m ≠ l → x m = y m
    · rw [if_pos hag]
      have hd := sum_diff k l hkl x y hag
      suffices H : ((∑ m, (-1 : ℂ) ^ (x m : ℕ)) - ∑ m, (-1 : ℂ) ^ (y m : ℕ)) *
          Tmat z₁ z₂ z₃ z₄ h (x k, x l) (y k, y l) = 0 by linear_combination (1 / 2 : ℂ) * H
      rw [hd]
      generalize x k = a, x l = b, y k = c, y l = e
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
        simp [Tmat, finProdFinEquiv, s] <;> norm_num
    · rw [if_neg hag]; ring
