-- Prove2me | solution 1 for DirKECC1549.Asm.bstate_scc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-16T06:17:52.637007+00:00
-- url     : https://prove2.me/submissions/77b62dc1-b8b8-4445-adf4-869a20157465

import Definitions.Def_DirKECC1549_Impl_SccBfs
import Theorems.Thm_DirKECC1549_Asm_kosaraju_key

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

theorem sc_symm (D : Fin m → Fin n × Fin n) {a b : Fin n} (h : StronglyConn D a b) :
    StronglyConn D b a := ⟨h.2, h.1⟩

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

theorem reach_edge (D : Fin m → Fin n × Fin n) (e : Fin m) : Reach D (D e).1 (D e).2 :=
  ⟨[e], IsWalk.cons e [] rfl (IsWalk.nil _)⟩

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

/-- A walk from `a ∈ S` to `b ∉ S` has an edge leaving `S`, with reachable tail and co-reachable
head. -/
theorem walk_exit2 (D : Fin m → Fin n × Fin n) (S : Finset (Fin n)) {a b : Fin n}
    {p : List (Fin m)} (hp : IsWalk D a p b) (ha : a ∈ S) (hb : b ∉ S) :
    ∃ e, (D e).1 ∈ S ∧ (D e).2 ∉ S ∧ Reach D a (D e).1 ∧ Reach D (D e).2 b := by
  induction hp with
  | nil => exact absurd ha hb
  | cons e p he hw ih =>
    by_cases h2 : (D e).2 ∈ S
    · obtain ⟨e', h1, h3, h4, h5⟩ := ih h2 hb
      exact ⟨e', h1, h3, reach_trans D (he ▸ reach_edge D e) h4, h5⟩
    · exact ⟨e, he ▸ ha, h2, he ▸ reach_refl D _, ⟨p, hw⟩⟩

end DirKECC1549.Asm
end

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main DirKECC1549.Main.CostAux
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem solution (D : Fin m → Fin n × Fin n) (pos : Fin n → ℕ) (hpos : Function.Injective pos)
    (hKP : KP D pos) (A : Finset (Fin n)) (hA : ∀ a b, StronglyConn D a b → a ∈ A → b ∈ A)
    (v : Fin n) (hvA : v ∉ A) (hmax : ∀ x, x ∉ A → pos x ≤ pos v) (q : List (Fin n))
    (hB : BState D A v q q.length) : ∀ u, u ∈ q ↔ StronglyConn D v u := by
  have hv : v ∈ q := by
    obtain ⟨h1, h2⟩ := hB.hd
    exact List.mem_of_mem_head? h2
  intro u
  constructor
  · intro hu
    have hr := hB.reach u hu
    refine ⟨kosaraju_key D pos hpos hKP Aᶜ (fun a b hab ha => by
      simp only [mem_compl] at ha ⊢
      exact fun hb => ha (hA b a (sc_symm D hab) hb)) v (by simpa using hvA)
      (fun x hx => hmax x (by simpa using hx)) u (by simpa using hB.disj u hu) hr, hr⟩
  · intro hvu
    by_contra hu
    obtain ⟨p, hp⟩ := hvu.2
    obtain ⟨e, h1, h2, h3, h4⟩ := walk_exit2 D (q.toFinset)ᶜ hp (by simpa using hu) (by simpa using hv)
    simp only [mem_compl, List.mem_toFinset, not_not] at h1 h2
    obtain ⟨i, hi, hqi⟩ := List.mem_iff_getElem.1 h2
    rcases hB.closed i hi e hqi.symm with h5 | h5
    · have : StronglyConn D v (D e).1 :=
        ⟨reach_trans D hvu.1 h3, reach_trans D (reach_edge D e) (hB.reach _ h2)⟩
      exact hvA (hA _ _ (sc_symm D this) h5)
    · exact h1 h5
