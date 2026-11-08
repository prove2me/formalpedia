-- Prove2me | solution 1 for FuchsThesis.HonestExpert.eq_2_50
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:51:52.361209+00:00
-- url     : https://prove2.me/submissions/25e14afe-ef79-448c-b5b8-820858dc7562

import Mathlib
import Definitions.Def_FuchsThesis_HonestExpert_KeepsHonest

namespace Aux_FuchsEq250

lemma split3 {n : ℕ} {i j : Fin n} (hij : i ≠ j) (g : Fin n → ℝ) :
    ∑ k, g k = g i + g j + ∑ k ∈ (Finset.univ.erase i).erase j, g k := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  ring

end Aux_FuchsEq250

open FuchsThesis.HonestExpert in
theorem solution {n : ℕ} (hn : 3 ≤ n) {F : Fin n → ℝ → ℝ} (hF : KeepsHonest F)
    {i j : Fin n} (hij : i ≠ j) {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hpr : p < r)
    (hqr : q < r) (hr : r < 1) :
    p * F i q + (r - p) * F j (r - q) ≤ p * F i p + (r - p) * F j (r - p) := by
  set c : ℝ := (1 - r) / ((n : ℝ) - 2) with hc
  have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hcpos : 0 < c := div_pos (by linarith) hn2
  have hji : j ≠ i := fun h => hij h.symm
  let P : Fin n → ℝ := fun k => if k = i then p else if k = j then r - p else c
  let Q : Fin n → ℝ := fun k => if k = i then q else if k = j then r - q else c
  have hcard : (((Finset.univ.erase i).erase j).card : ℝ) = (n : ℝ) - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  have hrest : ∀ k ∈ (Finset.univ.erase i).erase j, P k = c ∧ Q k = c := by
    intro k hk
    have h1 : k ≠ j := Finset.ne_of_mem_erase hk
    have h2 : k ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    simp [P, Q, h1, h2]
  have hsumc : ∑ k ∈ (Finset.univ.erase i).erase j, c = 1 - r := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard, hc]
    field_simp
  have hP : IsPosDist P := by
    refine ⟨fun k => ?_, ?_⟩
    · simp only [P]; split_ifs <;> linarith
    · rw [Aux_FuchsEq250.split3 hij]
      rw [Finset.sum_congr rfl (fun k hk => (hrest k hk).1), hsumc]
      simp [P, hji]
  have hQ : IsPosDist Q := by
    refine ⟨fun k => ?_, ?_⟩
    · simp only [Q]; split_ifs <;> linarith
    · rw [Aux_FuchsEq250.split3 hij]
      rw [Finset.sum_congr rfl (fun k hk => (hrest k hk).2), hsumc]
      simp [Q, hji]
  have heq : ∑ k ∈ (Finset.univ.erase i).erase j, P k * F k (Q k)
      = ∑ k ∈ (Finset.univ.erase i).erase j, P k * F k (P k) :=
    Finset.sum_congr rfl (fun k hk => by rw [(hrest k hk).1, (hrest k hk).2])
  have hL : ∑ k, P k * F k (Q k) = P i * F i (Q i) + P j * F j (Q j)
      + ∑ k ∈ (Finset.univ.erase i).erase j, P k * F k (P k) := by
    rw [Aux_FuchsEq250.split3 hij (fun k => P k * F k (Q k)), heq]
  have hR : ∑ k, P k * F k (P k) = P i * F i (P i) + P j * F j (P j)
      + ∑ k ∈ (Finset.univ.erase i).erase j, P k * F k (P k) :=
    Aux_FuchsEq250.split3 hij (fun k => P k * F k (P k))
  have e1 : P i = p := if_pos rfl
  have e2 : P j = r - p := by
    show (if j = i then p else if j = j then r - p else c) = r - p
    rw [if_neg hji, if_pos rfl]
  have e3 : Q i = q := if_pos rfl
  have e4 : Q j = r - q := by
    show (if j = i then q else if j = j then r - q else c) = r - q
    rw [if_neg hji, if_pos rfl]
  rw [e1, e2, e3, e4] at hL
  rw [e1, e2] at hR
  have h := hF P Q hP hQ
  linarith
