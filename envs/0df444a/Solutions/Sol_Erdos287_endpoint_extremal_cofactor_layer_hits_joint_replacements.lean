-- Prove2me | solution 1 for Erdos287.endpoint_extremal_cofactor_layer_hits_joint_replacements
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-27T01:14:54.596265+00:00
-- url     : https://prove2.me/submissions/e0cb1fb4-54c0-465b-aadb-05d51a1a5318

import Mathlib
import Theorems.Thm_Erdos287_endpoint_extremal_cofactor_layer_hits_splits
import Theorems.Thm_Erdos287_endpoint_extremal_cover_trimmed_mass_obstruction

open Finset

set_option autoImplicit false

/-- The prime-power layer containing both endpoints must pass the carry test
and meet every in-range replacement for the sum of both endpoint reciprocals. -/
theorem solution (D : Finset ℕ) (p e c d L j : ℕ) (hp : p.Prime) (he : 1 ≤ e)
    (hcd : c < d) (hLp : p ^ j ∣ L) :
    let q := p ^ e
    let m := c * q
    let M := d * q
    let C := (Finset.Icc c d).filter (fun a => a * q ∈ D)
    1 < m → m ∈ D → M ∈ D → D ⊆ Finset.Icc m M →
    (∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D) →
    (∑ n ∈ D, (1 : ℚ) / n = 1) →
    (∀ (a b : ℕ) (F : Finset ℕ), 1 < a → a ∈ F → b ∈ F →
      F ⊆ Finset.Icc a b → (∀ x, a ≤ x → x + 1 ≤ b → x ∈ F ∨ x + 1 ∈ F) →
      (∑ n ∈ F, (1 : ℚ) / n = 1) → M ≤ b ∧ (b = M → a ≤ m)) →
    (∀ a ∈ Finset.Icc c d, a ∣ L) →
    c ∈ C ∧ d ∈ C ∧ p ^ (j + 1) ∣ (∑ a ∈ C, L / a) ∧
      ∀ A ⊆ Finset.Ioo c d, (∑ a ∈ A, (1 : ℚ) / a = 1 / (c : ℚ) + 1 / (d : ℚ)) →
        ∃ a ∈ A, a ∈ C := by
  classical
  intro q m M C hm hmD hMD hD hcover hsum hEnd hL
  have hq : 0 < q := pow_pos hp.pos _
  have hquot : M / p ^ e = d := Nat.mul_div_cancel _ hq
  have hL' : ∀ a ∈ Icc c (M / p ^ e), a ∣ L := by simpa only [hquot] using hL
  have hCarry := Erdos287.endpoint_extremal_cofactor_layer_hits_splits D p e c M L j
    hp he hLp hm hmD hD hcover hsum hEnd hL'
  rw [hquot] at hCarry
  obtain ⟨hcC, hDiv, _⟩ := hCarry
  have hdC : d ∈ C := mem_filter.mpr ⟨mem_Icc.mpr ⟨hcd.le, le_rfl⟩, hMD⟩
  refine ⟨hcC, hdC, hDiv, ?_⟩
  intro A hA hexact
  by_contra! hmiss
  let B := A.image (fun a => a * q)
  have hB : B ⊆ Icc (m + 1) (M - 1) := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hn
    obtain ⟨hla, hau⟩ := mem_Ioo.mp (hA ha)
    have hlo := Nat.mul_lt_mul_of_pos_right hla hq
    have hhi := Nat.mul_lt_mul_of_pos_right hau hq
    exact mem_Icc.mpr (by dsimp [m, M]; omega)
  have hBD : Disjoint B D := disjoint_left.mpr (fun {n} hn hnd => by
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hn
    obtain ⟨hla, hau⟩ := mem_Ioo.mp (hA ha)
    exact hmiss a ha (mem_filter.mpr ⟨mem_Icc.mpr ⟨hla.le, hau.le⟩, hnd⟩))
  have hmM : m < M := Nat.mul_lt_mul_of_pos_right hcd hq
  have hTrim : D.filter (fun n => n < m + 1 ∨ M - 1 < n) = {m, M} := by
    ext n
    simp only [mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hn, hnm⟩
      have hi := mem_Icc.mp (hD hn)
      omega
    · rintro (rfl | rfl)
      · exact ⟨hmD, Or.inl (by omega)⟩
      · exact ⟨hMD, Or.inr (by omega)⟩
  have hInj : Function.Injective (fun a : ℕ => a * q) :=
    fun _ _ h => Nat.eq_of_mul_eq_mul_right hq h
  have hEq : ∑ n ∈ B, (1 : ℚ) / n = 1 / (m : ℚ) + 1 / (M : ℚ) := by
    change (∑ n ∈ A.image (fun a => a * q), (1 : ℚ) / n) = _
    rw [sum_image hInj.injOn]
    calc
      (∑ a ∈ A, (1 : ℚ) / ((a * q : ℕ) : ℚ)) = ∑ a ∈ A, ((1 : ℚ) / a) / q := by
        apply sum_congr rfl
        intro a _
        rw [Nat.cast_mul, div_div]
      _ = 1 / (m : ℚ) + 1 / (M : ℚ) := by
        rw [← sum_div, hexact, add_div, div_div, div_div, ← Nat.cast_mul, ← Nat.cast_mul]
  have hblock := Erdos287.endpoint_extremal_cover_trimmed_mass_obstruction D B m M
    (m + 1) (M - 1) hm hcover hsum hEnd (by omega) (by omega) (Or.inr (by omega)) hB hBD
  rw [hTrim, sum_insert (by simpa using hmM.ne), sum_singleton] at hblock
  exact hblock hEq

