-- Prove2me | solution 1 for Erdos287.nine_groups_with_two_scale_distances
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T09:01:02.322739+00:00
-- url     : https://prove2.me/submissions/10d397e0-c88a-4e6c-810f-5394710e9b49

import Mathlib

set_option autoImplicit false

private theorem ordered_distance (L B u v i j : ℕ)
    (hu : u ≤ B) (hv : v ≤ B) (hij : i < j) (hj : j < 3) (hBL : B < L) :
    i * L + u < j * L + v ∧
      L ≤ (j * L + v - (i * L + u)) + B ∧
      j * L + v - (i * L + u) ≤ 2 * L + B := by
  have hlow := Nat.mul_le_mul_right L (show 1 ≤ j - i by omega)
  have hupp := Nat.mul_le_mul_right L (show j - i ≤ 2 by omega)
  have heq : (j - i) * L + i * L = j * L := by
    rw [← add_mul, Nat.sub_add_cancel hij.le]
  rw [one_mul] at hlow
  omega

/-- Nine equal groups with all cross-group distances in two prescribed scale bands. -/
theorem solution (D E K : ℕ) (hK : 0 < K) (hD : 1000 * K ≤ D) (hE : 64 * D ≤ E) :
    ∃ z : (Fin 3 × Fin 3) × Fin K → ℕ, Function.Injective z ∧
      (∀ i, z i ≤ 2 * E + 2 * D + K) ∧
      ∀ i j : (Fin 3 × Fin 3) × Fin K, i.1 ≠ j.1 → z i < z j →
        let d := z j - z i
        let L := if i.1.2 = j.1.2 then D else E
        25 * d ≥ 24 * L ∧ 25 * d ≤ 51 * L := by
  let z (i : (Fin 3 × Fin 3) × Fin K) := i.1.2.val * E + (i.1.1.val * D + i.2.val)
  have hsmall (i : (Fin 3 × Fin 3) × Fin K) :
      i.1.1.val * D + i.2.val ≤ 2 * D + K := by
    have hd := Nat.mul_le_mul_right D (show i.1.1.val ≤ 2 by omega)
    have hk := i.2.isLt
    omega
  have hlarge (i j : (Fin 3 × Fin 3) × Fin K) (h : i.1.2 < j.1.2) :
      z i < z j ∧ E ≤ (z j - z i) + (2 * D + K) ∧
        z j - z i ≤ 2 * E + (2 * D + K) :=
    ordered_distance E (2 * D + K) _ _ _ _ (hsmall i) (hsmall j)
      h j.1.2.isLt (by omega)
  have hshort (i j : (Fin 3 × Fin 3) × Fin K) (heq : i.1.2 = j.1.2)
      (h : i.1.1 < j.1.1) :
      z i < z j ∧ D ≤ (z j - z i) + K ∧ z j - z i ≤ 2 * D + K := by
    have hd := ordered_distance D K i.2.val j.2.val _ _ i.2.isLt.le j.2.isLt.le
      h j.1.1.isLt (by omega)
    dsimp [z]
    rw [heq]
    omega
  refine ⟨z, ?_, ?_, ?_⟩
  · intro i j h
    have heq : i.1.2 = j.1.2 := by
      rcases lt_trichotomy i.1.2 j.1.2 with hlt | heq | hgt
      · exact False.elim ((hlarge i j hlt).1.ne h)
      · exact heq
      · exact False.elim ((hlarge j i hgt).1.ne h.symm)
    have hlo : i.1.1 = j.1.1 := by
      rcases lt_trichotomy i.1.1 j.1.1 with hlt | hlo | hgt
      · exact False.elim ((hshort i j heq hlt).1.ne h)
      · exact hlo
      · exact False.elim ((hshort j i heq.symm hgt).1.ne h.symm)
    have hk : i.2 = j.2 := by
      apply Fin.ext
      dsimp [z] at h
      rw [heq, hlo] at h
      omega
    exact Prod.ext (Prod.ext hlo heq) hk
  · intro i
    have h := Nat.mul_le_mul_right E (show i.1.2.val ≤ 2 by omega)
    have hs := hsmall i
    dsimp [z]
    omega
  · intro i j hne hij
    dsimp only
    by_cases heq : i.1.2 = j.1.2
    · rw [if_pos heq]
      have hlo : i.1.1 < j.1.1 := by
        rcases lt_trichotomy i.1.1 j.1.1 with hlt | hlo | hgt
        · exact hlt
        · exact False.elim (hne (Prod.ext hlo heq))
        · exact False.elim ((hshort j i heq.symm hgt).1.asymm hij)
      obtain ⟨_, h₁, h₂⟩ := hshort i j heq hlo
      omega
    · rw [if_neg heq]
      have hhi : i.1.2 < j.1.2 := by
        rcases lt_or_gt_of_ne heq with hlt | hgt
        · exact hlt
        · exact False.elim ((hlarge j i hgt).1.asymm hij)
      obtain ⟨_, h₁, h₂⟩ := hlarge i j hhi
      omega

