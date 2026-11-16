-- Prove2me | solution 1 for DirKECC1549.Asm.sc_n_le_m
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-16T04:00:22.007202+00:00
-- url     : https://prove2.me/submissions/dcd051b5-e0e0-4eb6-9806-36ed81b59b67

import Definitions.Def_DirKECC1549_Impl_MainMath

set_option autoImplicit false

set_option autoImplicit false
open Classical Finset DirKECC1549.Main
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem solution (D : Fin m → Fin n × Fin n) (h : IsStronglyConnected D) (hn : 2 ≤ n) :
    n ≤ m := by
  have hout : ∀ v : Fin n, ∃ e : Fin m, (D e).1 = v := by
    intro v
    obtain ⟨u, hu⟩ : ∃ u : Fin n, u ≠ v := by
      by_cases hv : (v : ℕ) = 0
      · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at hv; simp at hv⟩
      · exact ⟨⟨0, by omega⟩, fun e => hv (by rw [← e])⟩
    obtain ⟨p, hp⟩ := (h v u).1
    cases hp with
    | nil => exact absurd rfl hu
    | cons e p he _ => exact ⟨e, he⟩
  choose g hg using hout
  have hinj : Function.Injective g := fun a b hab => by rw [← hg a, ← hg b, hab]
  simpa using Fintype.card_le_of_injective g hinj
