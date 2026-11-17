-- Prove2me | solution 1 for DirKECC1549.Asm.dstate_skip
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-16T06:13:51.206203+00:00
-- url     : https://prove2.me/submissions/f604b1f3-03da-41ac-ac47-0c78feca0a0d

import Definitions.Def_DirKECC1549_Impl_SccDfs

set_option autoImplicit false

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main DirKECC1549.Main.CostAux
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem solution (D : Fin m → Fin n × Fin n) (σ : Equiv.Perm (Fin m)) (stk po : List (Fin n))
    (v : Fin n) (hv : v ∈ stk) (ptr : Fin n → ℕ) (h : DState D σ stk po ptr) (i : Fin m)
    (hi : (i : ℕ) = ptr v) (hp : ptr v < ots D (v + 1))
    (ht : (D (σ i)).2 ∈ stk ∨ (D (σ i)).2 ∈ po) :
    DState D σ stk po (Function.update ptr v (ptr v + 1)) := by
  have hu : ∀ w, w ≠ v → Function.update ptr v (ptr v + 1) w = ptr w :=
    fun w h1 => Function.update_of_ne h1 _ _
  constructor
  · exact h.nd
  · intro w hw
    by_cases hwv : w = v
    · subst hwv; rw [Function.update_self]; have := h.plo w hw; omega
    · rw [hu w hwv]; exact h.plo w hw
  · intro w hw
    by_cases hwv : w = v
    · subst hwv; rw [Function.update_self]; omega
    · rw [hu w hwv]; exact h.phi w hw
  · intro w hw j hj1 hj2
    by_cases hwv : w = v
    · subst hwv
      rw [Function.update_self] at hj2
      rcases Nat.lt_or_ge (j : ℕ) (ptr w) with hj | hj
      · exact h.pex w hw j hj1 hj
      · have : j = i := Fin.ext (by omega)
        subst this; exact ht
    · rw [hu w hwv] at hj2; exact h.pex w hw j hj1 hj2
  · exact h.chain
  · exact h.S2
  · exact h.H
