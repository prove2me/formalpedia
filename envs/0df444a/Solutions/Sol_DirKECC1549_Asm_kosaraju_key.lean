-- Prove2me | solution 1 for DirKECC1549.Asm.kosaraju_key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-16T06:13:53.919121+00:00
-- url     : https://prove2.me/submissions/7258b4a6-8090-4628-be5c-12276e37f0ac

import Definitions.Def_DirKECC1549_Impl_SccMath

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

theorem sc_refl (D : Fin m → Fin n × Fin n) (a : Fin n) : StronglyConn D a a :=
  ⟨⟨[], IsWalk.nil a⟩, ⟨[], IsWalk.nil a⟩⟩

/-! ## Strongly connected components -/

end DirKECC1549.Main.CostAux
end

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

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main DirKECC1549.Main.CostAux
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem solution (D : Fin m → Fin n × Fin n) (pos : Fin n → ℕ) (hpos : Function.Injective pos)
    (hKP : KP D pos) (U : Finset (Fin n))
    (hU : ∀ a b, StronglyConn D a b → a ∈ U → b ∈ U) (v : Fin n) (hv : v ∈ U)
    (hmax : ∀ x ∈ U, pos x ≤ pos v) (u : Fin n) (hu : u ∈ U) (huv : Reach D u v) :
    Reach D v u := by
  by_contra hvu
  set C := univ.filter (fun z => StronglyConn D u z)
  have hC : C.Nonempty := ⟨u, by simp [C, sc_refl]⟩
  obtain ⟨x, hxC, hxmax⟩ := C.exists_max_image pos hC
  have hxs : StronglyConn D u x := by simpa [C] using hxC
  have hxU : x ∈ U := hU u x hxs hu
  have hxv : pos x < pos v := by
    rcases lt_or_eq_of_le (hmax x hxU) with h | h
    · exact h
    · exact absurd (reach_trans D (by rw [hpos h]; exact reach_refl D v) hxs.2) hvu
  obtain ⟨g, hg1, hg2, hg3⟩ := hKP x v (reach_trans D hxs.2 huv)
    (fun h => hvu (reach_trans D h hxs.2)) hxv
  have : g ∈ C := by
    simp only [C, mem_filter, mem_univ, true_and]
    exact ⟨reach_trans D hxs.1 hg2, reach_trans D hg1 hxs.2⟩
  have := hxmax g this
  omega
