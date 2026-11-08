-- Prove2me | solution 1 for FuchsThesis.HonestExpert.eq_2_54_2_56
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:58:51.008357+00:00
-- url     : https://prove2.me/submissions/c8c7fa49-ed23-4b8c-922d-ed819a6d6a06

import Mathlib
import Definitions.Def_FuchsThesis_HonestExpert_KeepsHonest

namespace Aux_Fuchs_HE_mono

lemma sum_diff {n : ℕ} (k l : Fin n) (hkl : l ≠ k) (f g : Fin n → ℝ)
    (h : ∀ j, j ≠ k → j ≠ l → f j = g j) :
    ∑ j, f j = ∑ j, g j + (f k - g k) + (f l - g l) := by
  have : ∀ j, f j = g j + ((if j = k then f k - g k else 0) + (if j = l then f l - g l else 0)) := by
    intro j
    by_cases hk : j = k
    · subst hk; simp [Ne.symm hkl]
    · by_cases hl : j = l
      · subst hl; simp [hk]
      · simp [hk, hl, h j hk hl]
  rw [Finset.sum_congr rfl (fun j _ => this j)]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma sum_V {n : ℕ} (k l : Fin n) (hkl : l ≠ k) (a b c : ℝ) :
    ∑ j : Fin n, (if j = k then a else if j = l then b else c) = n * c + (a - c) + (b - c) := by
  have : ∀ j : Fin n, (if j = k then a else if j = l then b else c)
      = c + ((if j = k then a - c else 0) + (if j = l then b - c else 0)) := by
    intro j
    by_cases hk : j = k
    · subst hk; simp [Ne.symm hkl]
    · by_cases hl : j = l
      · subst hl; simp [hk]
      · simp [hk, hl]
  rw [Finset.sum_congr rfl (fun j _ => this j)]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end Aux_Fuchs_HE_mono

open FuchsThesis.HonestExpert Aux_Fuchs_HE_mono in
theorem solution {n : ℕ} (hn : 3 ≤ n) {F : Fin n → ℝ → ℝ} (hF : KeepsHonest F) (k : Fin n) :
    MonotoneOn (F k) (Set.Ioo 0 1) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with h | h
  · rw [h]
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  obtain ⟨l, hlk⟩ := exists_ne k
  have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set s := (1 - y) / 2 with hs
  set d := y - x with hd
  set c := (1 - y) / 2 / ((n : ℝ) - 2) with hc
  have hspos : 0 < s := by rw [hs]; linarith
  have hdpos : 0 < d := by rw [hd]; linarith
  have hcpos : 0 < c := by rw [hc]; exact div_pos (by linarith) hn2
  have hnc : (n : ℝ) * c = 2 * c + (1 - y) / 2 := by
    rw [hc]; field_simp; ring
  set P : Fin n → ℝ := fun j => if j = k then y else if j = l then s else c with hP
  set Q : Fin n → ℝ := fun j => if j = k then x else if j = l then s + d else c with hQ
  have hPk : P k = y := by simp [hP]
  have hPl : P l = s := by simp [hP, hlk]
  have hQk : Q k = x := by simp [hQ]
  have hQl : Q l = s + d := by simp [hQ, hlk]
  have hPQ : ∀ j, j ≠ k → j ≠ l → P j = Q j := by
    intro j h1 h2; simp [hP, hQ, h1, h2]
  have hPd : IsPosDist P := by
    refine ⟨fun j => ?_, ?_⟩
    · simp only [hP]; split_ifs <;> assumption
    · simp only [hP]; rw [sum_V k l hlk, hnc, hs]; ring
  have hQd : IsPosDist Q := by
    refine ⟨fun j => ?_, ?_⟩
    · simp only [hQ]; split_ifs
      · exact hx0
      · linarith
      · exact hcpos
    · simp only [hQ]; rw [sum_V k l hlk, hnc, hs, hd]; ring
  have h1 := hF P Q hPd hQd
  have h2 := hF Q P hQd hPd
  rw [sum_diff k l hlk (fun j => P j * F j (P j)) (fun j => P j * F j (Q j))
    (fun j h1 h2 => by simp only [hPQ j h1 h2])] at h1
  rw [sum_diff k l hlk (fun j => Q j * F j (Q j)) (fun j => Q j * F j (P j))
    (fun j h1 h2 => by simp only [hPQ j h1 h2])] at h2
  simp only [hPk, hPl, hQk, hQl] at h1 h2
  by_contra hlt
  push_neg at hlt
  set a := F k y - F k x with ha
  set b := F l (s + d) - F l s with hb
  have hapos : a < 0 := by rw [ha]; linarith
  have e1 : s * b ≤ y * a := by rw [ha, hb]; linarith
  have e2 : x * a ≤ (s + d) * b := by rw [ha, hb]; linarith
  have e3 : s * (x * a) ≤ s * ((s + d) * b) := mul_le_mul_of_nonneg_left e2 hspos.le
  have e4 : (s + d) * (s * b) ≤ (s + d) * (y * a) := mul_le_mul_of_nonneg_left e1 (by linarith)
  have e5 : (s * x - (s + d) * y) * a ≤ 0 := by nlinarith
  have e6 : s * x - (s + d) * y < 0 := by nlinarith
  nlinarith
