-- Prove2me | solution 1 for DirKECC1549.Asm.dfsH_finish
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-16T06:13:55.027489+00:00
-- url     : https://prove2.me/submissions/788f9040-9ef1-4590-9302-6f305cfd7065

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

/-- A walk from `a ∈ S` to `b ∉ S` has an edge leaving `S` whose head is reachable from `a`. -/
theorem walk_exit (D : Fin m → Fin n × Fin n) (S : Finset (Fin n)) {a b : Fin n}
    {p : List (Fin m)} (hp : IsWalk D a p b) (ha : a ∈ S) (hb : b ∉ S) :
    ∃ e, (D e).1 ∈ S ∧ (D e).2 ∉ S ∧ Reach D a (D e).2 := by
  induction hp with
  | nil => exact absurd ha hb
  | cons e p he hw ih =>
    by_cases h2 : (D e).2 ∈ S
    · obtain ⟨e', h1, h3, h4⟩ := ih h2 hb
      exact ⟨e', h1, h3, reach_trans D (he ▸ reach_edge D e) h4⟩
    · exact ⟨e, he ▸ ha, h2, he ▸ reach_edge D e⟩

end DirKECC1549.Asm

namespace DirKECC1549.Asm

end DirKECC1549.Asm
end

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main DirKECC1549.Main.CostAux
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem solution (D : Fin m → Fin n × Fin n) (fin : Finset (Fin n)) (pos : Fin n → ℕ)
    (gray : Finset (Fin n)) (z : Fin n) (hz : z ∉ fin) (hzg : z ∈ gray)
    (hdisj : ∀ x ∈ fin, x ∉ gray)
    (hH : DfsH D fin pos)
    (hS2 : ∀ e, (D e).1 ∈ insert z fin → (D e).2 ∈ insert z fin ∨ (D e).2 ∈ gray)
    (hchain : ∀ g ∈ gray, Reach D g z)
    (pz : ℕ) (hpz : ∀ x ∈ fin, pos x < pz) :
    DfsH D (insert z fin) (Function.update pos z pz) := by
  have hpos : ∀ x ∈ fin, Function.update pos z pz x = pos x := fun x hx =>
    Function.update_of_ne (by rintro rfl; exact hz hx) _ _
  -- the new vertex
  have hz' : ∀ y, Reach D z y → ¬ Reach D y z → y ∉ insert z fin →
      ∃ g, Reach D g z ∧ Reach D z g ∧ g ∉ insert z fin := by
    intro y hzy hyz hy
    obtain ⟨p, hp⟩ := hzy
    obtain ⟨e, he1, he2, he3⟩ := walk_exit D (insert z fin) hp (mem_insert_self _ _) hy
    have hg : (D e).2 ∈ gray := (hS2 e he1).resolve_left he2
    exact ⟨(D e).2, hchain _ hg, he3, he2⟩
  intro x hx y hxy hyx
  rcases mem_insert.1 hx with rfl | hxf
  · by_cases hy : y ∈ insert x fin
    · left
      refine ⟨hy, ?_⟩
      rcases mem_insert.1 hy with rfl | hyf
      · exact absurd (reach_refl D y) hyx
      · rw [Function.update_self, hpos y hyf]; exact hpz y hyf
    · right
      obtain ⟨g, h1, h2, h3⟩ := hz' y hxy hyx hy
      exact ⟨g, h1, h2, Or.inl h3⟩
  · rcases hH x hxf y hxy hyx with ⟨h1, h2⟩ | ⟨g, h1, h2, h3⟩
    · left; exact ⟨mem_insert_of_mem h1, by rw [hpos y h1, hpos x hxf]; exact h2⟩
    · by_cases hgz : g = z
      · subst hgz
        by_cases hy : y ∈ insert g fin
        · rcases mem_insert.1 hy with rfl | hyf
          · exact absurd h1 hyx
          · right
            exact ⟨g, h1, h2, Or.inr ⟨mem_insert_self _ _, hy,
              by rw [Function.update_self, hpos y hyf]; exact hpz y hyf⟩⟩
        · right
          obtain ⟨g', h1', h2', h3'⟩ := hz' y (reach_trans D h1 hxy)
            (fun h => hyx (reach_trans D h h1)) hy
          exact ⟨g', reach_trans D h1' h1, reach_trans D h2 h2', Or.inl h3'⟩
      · right
        refine ⟨g, h1, h2, ?_⟩
        rcases h3 with h3 | ⟨h4, h5, h6⟩
        · left; rw [mem_insert]; push Not; exact ⟨hgz, h3⟩
        · right
          refine ⟨mem_insert_of_mem h4, mem_insert_of_mem h5, ?_⟩
          rw [hpos y h5, hpos g h4]; exact h6
