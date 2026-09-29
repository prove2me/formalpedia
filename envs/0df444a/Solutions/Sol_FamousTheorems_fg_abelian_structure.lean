-- Prove2me | solution 1 for FamousTheorems.fg_abelian_structure
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T07:15:02.22226+00:00
-- url     : https://prove2.me/submissions/cacf8b32-1567-4fee-9dfa-c70e09a95250

import Mathlib

universe u v

open Filter Set Topology DirectSum

theorem solution (G : Type u) [AddCommGroup G] [AddGroup.FG G] :
    ∃ (n : ℕ) (ι : Type) (_ : Fintype ι) (p : ι → ℕ) (_ : ∀ i, Nat.Prime <| p i) (e : ι → ℕ),
      Nonempty <| G ≃+ (Fin n →₀ ℤ) × ⨁ i : ι, ZMod (p i ^ e i) :=
  AddCommGroup.equiv_free_prod_directSum_zmod G
