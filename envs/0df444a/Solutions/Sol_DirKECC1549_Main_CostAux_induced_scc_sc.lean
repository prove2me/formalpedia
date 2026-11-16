-- Prove2me | solution 1 for DirKECC1549.Main.CostAux.induced_scc_sc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-16T04:00:12.174618+00:00
-- url     : https://prove2.me/submissions/6369b798-0527-4820-80a3-ce5452e574e5

import Definitions.Def_DirKECC1549_Impl_GraphAux

set_option autoImplicit false

section
set_option autoImplicit false

open Classical Finset

namespace DirKECC1549.Main.CostAux

open DirKECC1549.Main

/-! ## Exponents -/

/-! ## Powers of `n` -/

/-! ## Combinatorial constants -/

/-! ## Walks and cuts -/

variable {n m : ℕ}

theorem walk_append (D : Fin m → Fin n × Fin n) {a b c : Fin n} {p q : List (Fin m)}
    (hp : IsWalk D a p b) (hq : IsWalk D b q c) : IsWalk D a (p ++ q) c := by
  induction hp with
  | nil => simpa using hq
  | cons e p he _ ih => exact IsWalk.cons e (p ++ q) he (ih hq)

theorem reach_trans (D : Fin m → Fin n × Fin n) {a b c : Fin n} (h1 : Reach D a b)
    (h2 : Reach D b c) : Reach D a c := by
  obtain ⟨p, hp⟩ := h1; obtain ⟨q, hq⟩ := h2; exact ⟨p ++ q, walk_append D hp hq⟩

/-! ## Strongly connected components -/

theorem mem_scc {D : Fin m → Fin n × Fin n} {u v : Fin n} : v ∈ sccOf D u ↔ StronglyConn D u v := by
  simp [sccOf]

theorem posIn_vertexOf (S : Finset (Fin n)) (i : Fin S.card) (h : vertexOf S i ∈ S) :
    posIn S (vertexOf S i) h = i := by
  have e : (⟨vertexOf S i, h⟩ : S) = S.orderIsoOfFin rfl i := Subtype.ext rfl
  unfold posIn; rw [e]; exact OrderIso.symm_apply_apply _ _

theorem vertexOf_mem (S : Finset (Fin n)) (i : Fin S.card) : vertexOf S i ∈ S :=
  (S.orderIsoOfFin rfl i).2

end DirKECC1549.Main.CostAux
end

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main
open DirKECC1549 DirKECC1549.Main.CostAux
variable {n m : ℕ}

theorem solution (hF : DirKECC1549.Asm.Facts) (D : Fin m → Fin n × Fin n) (u : Fin n) :
    IsStronglyConnected (induced D (sccOf D u)) := by
  set S := sccOf D u
  have key : ∀ i j : Fin S.card, Reach (induced D S) i j := by
    intro i j
    have hx := vertexOf_mem S i
    have hy := vertexOf_mem S j
    have sx : StronglyConn D u (vertexOf S i) := mem_scc.1 hx
    have sy : StronglyConn D u (vertexOf S j) := mem_scc.1 hy
    obtain ⟨p, hp⟩ := reach_trans D sx.2 sy.1
    obtain ⟨q, -, hq⟩ := hF.lift D S _ _ hx hy p hp (hF.walks D u _ _ sx sy p hp)
    rw [posIn_vertexOf, posIn_vertexOf] at hq
    exact ⟨q, hq⟩
  exact fun i j => ⟨key i j, key j i⟩
