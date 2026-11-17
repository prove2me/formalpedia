-- Prove2me | solution 1 for DirKECC1549.Asm.dstate_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-16T06:13:48.741024+00:00
-- url     : https://prove2.me/submissions/363a5585-0116-4807-a989-13346f976b4f

import Definitions.Def_DirKECC1549_Impl_SccDfs

set_option autoImplicit false

section
set_option autoImplicit false

open Classical Finset

namespace DirKECC1549.Asm

open DirKECC1549.Main DirKECC1549.Main.CostAux

variable {n m : ℕ}

theorem reach_refl (D : Fin m → Fin n × Fin n) (a : Fin n) : Reach D a a := ⟨[], IsWalk.nil a⟩

end DirKECC1549.Asm

namespace DirKECC1549.Asm

end DirKECC1549.Asm
end

section
set_option autoImplicit false

open Classical Finset

namespace DirKECC1549.Asm

open DirKECC1549.Main DirKECC1549.Main.CostAux

variable {n m : ℕ}

theorem ots_mono (D : Fin m → Fin n × Fin n) {a b : ℕ} (h : a ≤ b) : ots D a ≤ ots D b := by
  unfold ots; exact card_le_card (fun e => by simp only [mem_filter, mem_univ, true_and]; omega)

end DirKECC1549.Asm
end

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main DirKECC1549.Main.CostAux
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem solution (D : Fin m → Fin n × Fin n) (σ : Equiv.Perm (Fin m)) (po : List (Fin n))
    (ptr : Fin n → ℕ) (h : DState D σ [] po ptr) (s : Fin n) (hs : s ∉ po) :
    DState D σ [s] po (Function.update ptr s (ots D s)) where
  nd := by simp only [List.singleton_append, List.nodup_cons]; exact ⟨hs, by simpa using h.nd⟩
  plo := fun v hv => by simp at hv; subst hv; simp
  phi := fun v hv => by simp at hv; subst hv; simp; exact ots_mono D (by omega)
  pex := fun v hv i h1 h2 => by simp at hv; subst hv; simp at h2; omega
  chain := fun i j hi hj _ => by
    simp at hi hj; subst hi; subst hj; exact reach_refl D _
  S2 := fun x hx e he => by
    rcases h.S2 x hx e he with h1 | h1
    · simp at h1
    · exact Or.inr h1
  H := h.H
