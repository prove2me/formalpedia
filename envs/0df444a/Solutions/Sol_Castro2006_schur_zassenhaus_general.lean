-- Prove2me | solution 1 for Castro2006.schur_zassenhaus_general
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T21:28:50.322208+00:00
-- url     : https://prove2.me/submissions/8ab3985d-9437-4b68-9c8c-3fd8d4cea224

import Mathlib

theorem solution {E : Type} [Group E] [Fintype E] (k m : ℕ)
    (hcard : Fintype.card E = k * m) (hcop : k.Coprime m)
    (A : Subgroup E) [A.Normal] (hA : Nat.card A = k) :
    ∃ H : Subgroup E, H.IsComplement' A := by
  apply Subgroup.exists_left_complement'_of_coprime
  have h1 := A.card_mul_index
  rw [Nat.card_eq_fintype_card (α := E), hcard, hA] at h1
  have hk : 0 < k := by
    rw [← hA]; exact Nat.card_pos
  have : A.index = m := Nat.eq_of_mul_eq_mul_left hk h1
  rw [hA, this]; exact hcop
