-- Prove2me | solution 1 for Conway99.conway_99_no_orbit_matrix
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-06T21:56:49.044754+00:00
-- url     : https://prove2.me/submissions/63af671d-cad7-4ba1-a017-cb358bcf9be0

import Mathlib
import Theorems.Thm_Conway99_no_orbit_matrix_of_diag_mem

open Finset

namespace ConwayDiag

/-- The constraints an orbit matrix for a hypothetical `(99,14,1,2)` graph must satisfy. -/
structure IsOrbitMatrix (C : Matrix (Fin 9) (Fin 9) ℕ) : Prop where
  symm : ∀ i j, C i j = C j i
  row : ∀ i, ∑ j, C i j = 14
  eq : ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22

variable {C : Matrix (Fin 9) (Fin 9) ℕ}

/-- The diagonal equation, with the symmetry folded in. -/
lemma sum_sq_add_diag (hC : IsOrbitMatrix C) (i : Fin 9) :
    (∑ k, C i k ^ 2) + C i i = 34 := by
  have h := hC.eq i i
  simp only [eq_self_iff_true, if_true] at h
  rw [show (∑ k, C i k ^ 2) = ∑ k, C i k * C k i from
    Finset.sum_congr rfl fun k _ => by rw [hC.symm k i, sq]]
  omega

/-- Every diagonal entry is even. -/
lemma diag_even (hC : IsOrbitMatrix C) (i : Fin 9) : C i i % 2 = 0 := by
  have hsq : ∀ n : ℕ, n ^ 2 % 2 = n % 2 := by
    intro n
    rcases Nat.even_or_odd n with h | h
    · obtain ⟨t, rfl⟩ := h; ring_nf; omega
    · obtain ⟨t, rfl⟩ := h; ring_nf; omega
  have hpar : (∑ k, C i k ^ 2) % 2 = 0 := by
    rw [Finset.sum_nat_mod]
    rw [show (∑ k, C i k ^ 2 % 2) = ∑ k, C i k % 2 from
      Finset.sum_congr rfl fun k _ => hsq _]
    rw [← Finset.sum_nat_mod, hC.row i]
  have h := sum_sq_add_diag hC i
  omega


/-- Every diagonal entry is at most `4`: Cauchy-Schwarz on the eight off-diagonal
entries of a row. -/
lemma diag_le_four (hC : IsOrbitMatrix C) (i : Fin 9) : C i i ≤ 4 := by
  classical
  set T : ℕ := ∑ k ∈ Finset.univ.erase i, C i k with hTdef
  set Q : ℕ := ∑ k ∈ Finset.univ.erase i, C i k ^ 2 with hQdef
  have hsplit1 : C i i + T = ∑ k, C i k :=
    Finset.add_sum_erase Finset.univ (fun k => C i k) (Finset.mem_univ i)
  have hsplit2 : C i i ^ 2 + Q = ∑ k, C i k ^ 2 :=
    Finset.add_sum_erase Finset.univ (fun k => C i k ^ 2) (Finset.mem_univ i)
  have hT : C i i + T = 14 := by rw [hsplit1, hC.row i]
  have hQ : C i i ^ 2 + Q + C i i = 34 := by
    rw [hsplit2]; exact sum_sq_add_diag hC i
  -- Cauchy-Schwarz over the eight off-diagonal entries
  have hcard : (Finset.univ.erase i).card = 8 := by simp
  have hcs : (T : ℤ) ^ 2 ≤ 8 * (Q : ℤ) := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := Finset.univ.erase i) (f := fun k => (C i k : ℤ))
    rw [hcard] at h
    have e1 : (∑ k ∈ Finset.univ.erase i, (C i k : ℤ)) = (T : ℤ) := by
      rw [hTdef]; push_cast; ring
    have e2 : (∑ k ∈ Finset.univ.erase i, (C i k : ℤ) ^ 2) = (Q : ℤ) := by
      rw [hQdef]; push_cast; ring
    rw [e1, e2] at h
    exact_mod_cast h
  have hle5 : C i i ≤ 5 := by nlinarith [hQ, Nat.zero_le Q]
  interval_cases h : C i i
  · omega
  · omega
  · omega
  · omega
  · omega
  · -- `C i i = 5` forces `T = 9` and `Q = 4`, contradicting Cauchy-Schwarz
    exfalso
    have hT9 : T = 9 := by omega
    have hQ4 : Q = 4 := by omega
    rw [hT9, hQ4] at hcs
    norm_num at hcs

/-- Every diagonal entry lies in `{0, 2, 4}`. -/
lemma diag_mem (hC : IsOrbitMatrix C) (i : Fin 9) :
    C i i = 0 ∨ C i i = 2 ∨ C i i = 4 := by
  have h1 := diag_le_four hC i
  have h2 := diag_even hC i
  omega

end ConwayDiag

open ConwayDiag

theorem solution :
    ¬ ∃ C : Matrix (Fin 9) (Fin 9) ℕ, (∀ i j, C i j = C j i) ∧ (∀ i, ∑ j, C i j = 14) ∧
      ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22 := by
  rintro ⟨C, hsym, hrow, heq⟩
  have hC : IsOrbitMatrix C := ⟨hsym, hrow, heq⟩
  exact Conway99.no_orbit_matrix_of_diag_mem ⟨C, hsym, hrow, heq, fun i => diag_mem hC i⟩
