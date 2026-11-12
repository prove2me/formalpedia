-- Prove2me | solution 1 for BunkbedAux.wzEdges_reach_iff
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T04:15:13.443679+00:00
-- url     : https://prove2.me/submissions/f7d3fe3e-a746-403a-adda-06f7ba11b690

import Definitions.Def_BunkbedHypergraph

/-!
# The WZ states realise their own partitions

`WZ.edges s (a,b,c) l` is the canonical edge set that the Wierman–Ziff state `s` contributes
inside the hyperedge `(a,b,c)` on level `l`.  Here we prove the two structural facts about it:

* `Bunkbed.Sub2.edges_support` — every edge of `WZ.edges s (a,b,c) l` has both endpoints among
  the three lifted vertices `(a,l), (b,l), (c,l)`;
* `Bunkbed.Sub2.reach_iff` — for **distinct** `a b c`, the reachability relation induced on
  `(a,l), (b,l), (c,l)` by `ofEdges (WZ.edges s (a,b,c) l)` is *exactly* the partition named by
  `s`: the canonical edge set joins the pairs `s` says it joins, and no others.

The `theorem solution` / `theorem edges_support` declarations at the end of the file are the
verbatim forms requested in the brief.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Bunkbed.Sub2

open Bunkbed Bunkbed.Hyper SimpleGraph Finset

variable {V : Type*} [DecidableEq V]

/-! ## Generic tools: reachability inside an adjacency-closed set -/

/-- A set closed under passing to adjacent vertices is closed under reachability. -/
lemma mem_of_reachable {W : Type*} {G : SimpleGraph W} {K : Set W}
    (hK : ∀ u v, G.Adj u v → u ∈ K → v ∈ K) :
    ∀ {x y : W}, G.Reachable x y → x ∈ K → y ∈ K := by
  intro x y h
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact id
  | cons hadj _ ih => exact fun hx => ih (hK _ _ hadj hx)

/-- An edge of `ofEdges S` really is a member of `S`. -/
lemma mem_of_adj {W : Type*} {S : Finset (Sym2 W)} {u v : W} (h : (ofEdges S).Adj u v) :
    s(u, v) ∈ S := by
  simpa using ((fromEdgeSet_adj (s := (S : Set (Sym2 W)))).mp h).1

/-- Separation criterion: if no edge of `S` crosses the boundary of `K`, then no vertex of `K`
reaches a vertex outside `K`.  (This is what rules out "long" walks: it needs no bound on the
length of the walk, only that each single step stays inside `K`.) -/
lemma not_reachable_of_sep {W : Type*} {S : Finset (Sym2 W)} {K : Set W} {x y : W}
    (hK : ∀ u v : W, s(u, v) ∈ S → (u ∈ K ↔ v ∈ K)) (hx : x ∈ K) (hy : y ∉ K) :
    ¬ (ofEdges S).Reachable x y := fun h =>
  hy (mem_of_reachable (fun _ _ hadj hu => (hK _ _ (mem_of_adj hadj)).mp hu) h hx)

/-- A single edge of `S` between distinct endpoints makes them reachable. -/
lemma reachable_of_mem {W : Type*} {S : Finset (Sym2 W)} {u v : W} (h : s(u, v) ∈ S)
    (hne : u ≠ v) : (ofEdges S).Reachable u v :=
  ((fromEdgeSet_adj (s := (S : Set (Sym2 W)))).mpr ⟨by simpa using h, hne⟩).reachable

/-! ## Fact 2: the canonical edge sets touch only the three lifted vertices -/

theorem edges_support (a b c : V) (l : Fin 2) (s : WZ) (e : Sym2 (V × Fin 2))
    (he : e ∈ WZ.edges s (a, b, c) l) (v : V × Fin 2) (hv : v ∈ e) :
    v = (a, l) ∨ v = (b, l) ∨ v = (c, l) := by
  cases s <;>
    simp only [WZ.edges, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty] at he
  · rcases he with rfl | rfl | rfl <;> (simp only [Sym2.mem_iff] at hv; tauto)
  · subst he; simp only [Sym2.mem_iff] at hv; tauto
  · subst he; simp only [Sym2.mem_iff] at hv; tauto
  · subst he; simp only [Sym2.mem_iff] at hv; tauto

/-! ## Fact 1: the induced reachability relation is exactly the named partition -/

/-- Distinct base vertices lift to distinct vertices on a common level. -/
private lemma lift_ne {x y : V} (h : x ≠ y) (l : Fin 2) : ((x, l) : V × Fin 2) ≠ (y, l) := by
  simp [Prod.ext_iff, h]

theorem reach_iff (a b c : V) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (l : Fin 2) (s : WZ) :
    ((ofEdges (WZ.edges s (a, b, c) l)).Reachable (a, l) (b, l) ↔ (s = WZ.abc ∨ s = WZ.ab_c))
    ∧ ((ofEdges (WZ.edges s (a, b, c) l)).Reachable (b, l) (c, l) ↔ (s = WZ.abc ∨ s = WZ.a_bc))
    ∧ ((ofEdges (WZ.edges s (a, b, c) l)).Reachable (a, l) (c, l) ↔
        (s = WZ.abc ∨ s = WZ.ac_b)) := by
  have hab' : ((a, l) : V × Fin 2) ≠ (b, l) := lift_ne hab l
  have hbc' : ((b, l) : V × Fin 2) ≠ (c, l) := lift_ne hbc l
  have hac' : ((a, l) : V × Fin 2) ≠ (c, l) := lift_ne hac l
  cases s
  -- `abc`: the full triangle, so all three pairs are joined
  · refine ⟨?_, ?_, ?_⟩
    · exact iff_of_true (reachable_of_mem (by simp [WZ.edges]) hab') (Or.inl rfl)
    · exact iff_of_true (reachable_of_mem (by simp [WZ.edges]) hbc') (Or.inl rfl)
    · exact iff_of_true (reachable_of_mem (by simp [WZ.edges]) hac') (Or.inl rfl)
  -- `ab_c`: the single edge `a — b`; the component `{a,b}` separates off `c`
  · have key : ∀ u v : V × Fin 2, s(u, v) ∈ WZ.edges WZ.ab_c (a, b, c) l →
        (u ∈ ({(a, l), (b, l)} : Set (V × Fin 2)) ↔ v ∈ ({(a, l), (b, l)} : Set (V × Fin 2))) := by
      intro u v hu
      simp only [WZ.edges, Finset.mem_singleton, Sym2.eq_iff] at hu
      rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;> simp
    refine ⟨?_, ?_, ?_⟩
    · exact iff_of_true (reachable_of_mem (by simp [WZ.edges]) hab') (Or.inr rfl)
    · exact iff_of_false
        (not_reachable_of_sep key (by simp) (by simp [hac.symm, hbc.symm])) (by decide)
    · exact iff_of_false
        (not_reachable_of_sep key (by simp) (by simp [hac.symm, hbc.symm])) (by decide)
  -- `ac_b`: the single edge `a — c`; `b` is isolated
  · have key : ∀ u v : V × Fin 2, s(u, v) ∈ WZ.edges WZ.ac_b (a, b, c) l →
        (u ∈ ({(b, l)} : Set (V × Fin 2)) ↔ v ∈ ({(b, l)} : Set (V × Fin 2))) := by
      intro u v hu
      simp only [WZ.edges, Finset.mem_singleton, Sym2.eq_iff] at hu
      rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;> simp [hab, hbc.symm]
    have key2 : ∀ u v : V × Fin 2, s(u, v) ∈ WZ.edges WZ.ac_b (a, b, c) l →
        (u ∈ ({(a, l), (c, l)} : Set (V × Fin 2)) ↔ v ∈ ({(a, l), (c, l)} : Set (V × Fin 2))) := by
      intro u v hu
      simp only [WZ.edges, Finset.mem_singleton, Sym2.eq_iff] at hu
      rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;> simp
    refine ⟨?_, ?_, ?_⟩
    · exact iff_of_false
        (not_reachable_of_sep key2 (by simp) (by simp [hab.symm, hbc])) (by decide)
    · exact iff_of_false (not_reachable_of_sep key (by simp) (by simp [hbc.symm])) (by decide)
    · exact iff_of_true (reachable_of_mem (by simp [WZ.edges]) hac') (Or.inr rfl)
  -- `a_bc`: the single edge `b — c`; `a` is isolated
  · have key : ∀ u v : V × Fin 2, s(u, v) ∈ WZ.edges WZ.a_bc (a, b, c) l →
        (u ∈ ({(a, l)} : Set (V × Fin 2)) ↔ v ∈ ({(a, l)} : Set (V × Fin 2))) := by
      intro u v hu
      simp only [WZ.edges, Finset.mem_singleton, Sym2.eq_iff] at hu
      rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;>
        simp [hab.symm, hac.symm]
    refine ⟨?_, ?_, ?_⟩
    · exact iff_of_false (not_reachable_of_sep key (by simp) (by simp [hab.symm])) (by decide)
    · exact iff_of_true (reachable_of_mem (by simp [WZ.edges]) hbc') (Or.inr rfl)
    · exact iff_of_false (not_reachable_of_sep key (by simp) (by simp [hac.symm])) (by decide)
  -- `a_b_c`: no edges at all, so every vertex is its own component
  · have key : ∀ (K : Set (V × Fin 2)) (u v : V × Fin 2),
        s(u, v) ∈ WZ.edges WZ.a_b_c (a, b, c) l → (u ∈ K ↔ v ∈ K) := by
      intro K u v hu
      simp [WZ.edges] at hu
    refine ⟨?_, ?_, ?_⟩
    · exact iff_of_false (not_reachable_of_sep (K := {((a, l) : V × Fin 2)}) (key _)
        (by simp) (by simp [hab.symm])) (by decide)
    · exact iff_of_false (not_reachable_of_sep (K := {((b, l) : V × Fin 2)}) (key _)
        (by simp) (by simp [hbc.symm])) (by decide)
    · exact iff_of_false (not_reachable_of_sep (K := {((a, l) : V × Fin 2)}) (key _)
        (by simp) (by simp [hac.symm])) (by decide)

end Bunkbed.Sub2

/-! ## The requested statements, verbatim -/

open Bunkbed Bunkbed.Hyper SimpleGraph

/-- **Fact 1.** The canonical edge set of a WZ state joins exactly the pairs the state names. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (a b c : V)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (l : Fin 2) (s : WZ) :
    ((ofEdges (WZ.edges s (a, b, c) l)).Reachable (a, l) (b, l) ↔ (s = WZ.abc ∨ s = WZ.ab_c))
    ∧ ((ofEdges (WZ.edges s (a, b, c) l)).Reachable (b, l) (c, l) ↔ (s = WZ.abc ∨ s = WZ.a_bc))
    ∧ ((ofEdges (WZ.edges s (a, b, c) l)).Reachable (a, l) (c, l) ↔ (s = WZ.abc ∨ s = WZ.ac_b)) :=
  Bunkbed.Sub2.reach_iff a b c hab hbc hac l s

/-- **Fact 2.** The canonical edge sets touch only the three lifted vertices. -/
theorem edges_support {V : Type*} [DecidableEq V] (a b c : V) (l : Fin 2) (s : WZ)
    (e : Sym2 (V × Fin 2)) (he : e ∈ WZ.edges s (a, b, c) l) (v : V × Fin 2) (hv : v ∈ e) :
    v = (a, l) ∨ v = (b, l) ∨ v = (c, l) :=
  Bunkbed.Sub2.edges_support a b c l s e he v hv

#print axioms solution
#print axioms edges_support
#print axioms Bunkbed.Sub2.reach_iff
#print axioms Bunkbed.Sub2.edges_support
