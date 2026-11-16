-- Prove2me | solution 1 for DirKECC1549.Asm.sortPerm_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-16T04:00:33.204006+00:00
-- url     : https://prove2.me/submissions/1148c398-0094-4536-996c-5292c182e58b

import Definitions.Def_DirKECC1549_Impl_LayComb

set_option autoImplicit false

section
set_option autoImplicit false

open Classical Finset

namespace DirKECC1549.Asm

variable {m : ℕ}

theorem sortPerm_posK (key : Fin m → ℕ) (e : Fin m) :
    sortPerm key ⟨posK key e, posK_lt_m key e⟩ = e := by
  unfold sortPerm
  rw [Equiv.symm_apply_eq]; rfl

end DirKECC1549.Asm
end

set_option autoImplicit false
open Classical Finset
open DirKECC1549 DirKECC1549.Asm
variable {m : ℕ}

theorem solution (key : Fin m → ℕ) : Monotone (fun i => key (sortPerm key i)) := by
  intro i j hij
  by_contra hlt
  push Not at hlt
  set e := sortPerm key i
  set e' := sortPerm key j
  have hi : (i : ℕ) = posK key e := by
    have := sortPerm_posK key e
    have h2 : (⟨posK key e, posK_lt_m key e⟩ : Fin m) = i := by
      apply (sortPerm key).injective; rw [this]
    rw [← h2]
  have hj : (j : ℕ) = posK key e' := by
    have := sortPerm_posK key e'
    have h2 : (⟨posK key e', posK_lt_m key e'⟩ : Fin m) = j := by
      apply (sortPerm key).injective; rw [this]
    rw [← h2]
  have h1 := posK_lt key e'
  have h2 := posK_ge key e
  have h3 := cntLT_mono key (show key e' + 1 ≤ key e by omega)
  have := Fin.le_def.1 hij
  omega
