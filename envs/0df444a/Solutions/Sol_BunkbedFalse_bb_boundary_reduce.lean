-- Prove2me | solution 1 for BunkbedFalse.bb_boundary_reduce
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T04:59:02.503849+00:00
-- url     : https://prove2.me/submissions/7638e36b-be14-47b7-b7b3-0a557ce632eb

import Definitions.Def_BunkbedSubstituted

/-!
# Bunkbed reachability depends only on the per-copy boundary partitions

In the bunkbed graph over the substituted graph `subEdges`, reachability between *lifted
hypergraph vertices* `(iota x, l)` depends on the open edge sets only through the partition each
gadget copy induces on its three attachment vertices, at each level -- and the result matches the
Wierman-Ziff graph on `Fin 10 × Fin 2`.

The two sides live on different vertex types (`Fin 7222 × Fin 2` versus `Fin 10 × Fin 2`), so the
argument is factored in two steps:

* a **substitution step** entirely on `Fin 7222 × Fin 2`, comparing the bunkbed graph with the
  Wierman-Ziff graph *transported along* `iota`, by the boundary-congruence principle
  (`bc_boundary_congr` below, a copy of the accepted `BunkbedAux.boundary_congr`), with boundary
  `bdryB` = the ten hypergraph vertices on the two levels; and
* a **relabelling step** (`reach_map_iff`), valid for any injective vertex map, which transports
  the transported Wierman-Ziff graph's reachability back to `Fin 10 × Fin 2`.
-/

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

open Bunkbed Bunkbed.Hyper SimpleGraph Finset

namespace Bunkbed.Sub3

open Bunkbed.Sub

/-! ## Generic facts about `ofEdges` -/

section Generic

variable {W : Type*}

lemma mem_of_adj {S : Finset (Sym2 W)} {u v : W} (h : (ofEdges S).Adj u v) : s(u, v) ∈ S := by
  simpa using ((fromEdgeSet_adj (s := (S : Set (Sym2 W)))).mp h).1

lemma adj_of_mem {S : Finset (Sym2 W)} {u v : W} (h : s(u, v) ∈ S) (hne : u ≠ v) :
    (ofEdges S).Adj u v :=
  (fromEdgeSet_adj (s := (S : Set (Sym2 W)))).mpr ⟨by simpa using h, hne⟩

lemma reachable_of_mem {S : Finset (Sym2 W)} {u v : W} (h : s(u, v) ∈ S) (hne : u ≠ v) :
    (ofEdges S).Reachable u v := (adj_of_mem h hne).reachable

/-- A predicate closed under passing to adjacent vertices is closed under reachability. -/
lemma prop_transport {G : SimpleGraph W} {P : W → Prop} (hstep : ∀ u v, G.Adj u v → P u → P v) :
    ∀ {x y : W}, G.Reachable x y → P x → P y := by
  intro x y h
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact id
  | cons hadj _ ih => exact fun hx => ih (hstep _ _ hadj hx)

lemma mem_of_reachable {G : SimpleGraph W} {K : Set W}
    (hK : ∀ u v, G.Adj u v → u ∈ K → v ∈ K) : ∀ {x y : W}, G.Reachable x y → x ∈ K → y ∈ K :=
  prop_transport hK

/-- If no edge of `S` crosses the boundary of `K`, no vertex of `K` reaches a vertex outside. -/
lemma not_reachable_of_sep {S : Finset (Sym2 W)} {K : Set W} {x y : W}
    (hK : ∀ u v : W, s(u, v) ∈ S → (u ∈ K ↔ v ∈ K)) (hx : x ∈ K) (hy : y ∉ K) :
    ¬ (ofEdges S).Reachable x y := fun h =>
  hy (mem_of_reachable (fun _ _ hadj hu => (hK _ _ (mem_of_adj hadj)).mp hu) h hx)

/-- If `u` is reachable from some *other* vertex, then `u` is covered by an edge. -/
lemma exists_edge_of_reachable_ne {T : Finset (Sym2 W)} {b u : W}
    (h : (ofEdges T).Reachable b u) (hne : b ≠ u) : ∃ f ∈ T, u ∈ f := by
  obtain ⟨p⟩ := h.symm
  cases p with
  | nil => exact absurd rfl hne
  | cons hadj q =>
    rw [SimpleGraph.fromEdgeSet_adj] at hadj
    exact ⟨_, Finset.mem_coe.1 hadj.1, by simp⟩

lemma flipIff {G₁ G₂ : SimpleGraph W} {u v : W} (h : G₁.Reachable u v ↔ G₂.Reachable u v) :
    G₁.Reachable v u ↔ G₂.Reachable v u :=
  ⟨fun hh => (h.1 hh.symm).symm, fun hh => (h.2 hh.symm).symm⟩

end Generic

/-! ## Relabelling along an injective vertex map -/

section Relabel

variable {A B : Type*} [DecidableEq B] {f : A → B}

lemma map_eq_pair : ∀ (g : Sym2 A) (p q : B), Sym2.map f g = s(p, q) →
    ∃ a b : A, g = s(a, b) ∧ f a = p ∧ f b = q := by
  intro g
  induction g using Sym2.ind with
  | _ a b =>
    intro p q h
    rw [Sym2.map_mk, Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨a, b, rfl, h1, h2⟩
    · exact ⟨b, a, Sym2.eq_swap, h2, h1⟩

lemma adj_map (hf : Function.Injective f) {E : Finset (Sym2 A)} {u v : A}
    (h : (ofEdges E).Adj u v) : (ofEdges (E.image (Sym2.map f))).Adj (f u) (f v) := by
  refine adj_of_mem ?_ (fun hh => h.ne (hf hh))
  have h2 := Finset.mem_image_of_mem (Sym2.map f) (mem_of_adj h)
  simpa using h2

lemma reach_map (hf : Function.Injective f) {E : Finset (Sym2 A)} :
    ∀ {u v : A}, (ofEdges E).Reachable u v →
      (ofEdges (E.image (Sym2.map f))).Reachable (f u) (f v) := by
  intro u v h
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | cons hadj _ ih => exact ((adj_map hf hadj).reachable).trans ih

lemma reach_of_map (hf : Function.Injective f) {E : Finset (Sym2 A)} {u v : A}
    (h : (ofEdges (E.image (Sym2.map f))).Reachable (f u) (f v)) : (ofEdges E).Reachable u v := by
  have step : ∀ p q : B, (ofEdges (E.image (Sym2.map f))).Adj p q →
      (∃ a, f a = p ∧ (ofEdges E).Reachable u a) → ∃ a, f a = q ∧ (ofEdges E).Reachable u a := by
    intro p q hadj hp
    obtain ⟨a, hfa, hra⟩ := hp
    obtain ⟨g, hg, hgpq⟩ := Finset.mem_image.1 (mem_of_adj hadj)
    obtain ⟨b, c, rfl, hb, hc⟩ := map_eq_pair g p q hgpq
    have hba : b = a := hf (by rw [hb, hfa])
    have hrb : (ofEdges E).Reachable u b := by rw [hba]; exact hra
    refine ⟨c, hc, hrb.trans (reachable_of_mem hg ?_)⟩
    intro hbc
    exact hadj.ne (by rw [← hb, ← hc, hbc])
  obtain ⟨a, hfa, hra⟩ := prop_transport step h ⟨u, rfl, Reachable.refl u⟩
  rw [← hf hfa]
  exact hra

/-- **Relabelling.**  Reachability is invariant under an injective relabelling of the vertices. -/
lemma reach_map_iff (hf : Function.Injective f) (E : Finset (Sym2 A)) (u v : A) :
    (ofEdges (E.image (Sym2.map f))).Reachable (f u) (f v) ↔ (ofEdges E).Reachable u v :=
  ⟨reach_of_map hf, reach_map hf⟩

end Relabel

/-! ## Boundary congruence (a copy of the accepted `BunkbedAux.boundary_congr`) -/

section Boundary

variable {V : Type*} [DecidableEq V] {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma reachable_union (S : ι → Finset (Sym2 V)) (i : ι) {p q : V}
    (h : (ofEdges (S i)).Reachable p q) : (ofEdges (univ.biUnion S)).Reachable p q :=
  h.mono (fromEdgeSet_mono
    (Finset.coe_subset.2 (Finset.subset_biUnion_of_mem S (mem_univ i))))

lemma adj_union_part {S : ι → Finset (Sym2 V)} {u v : V}
    (h : (ofEdges (univ.biUnion S)).Adj u v) :
    ∃ i, (ofEdges (S i)).Adj u v ∧ s(u, v) ∈ S i := by
  rw [SimpleGraph.fromEdgeSet_adj] at h
  obtain ⟨hmem, hne⟩ := h
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hmem)
  exact ⟨i, (SimpleGraph.fromEdgeSet_adj _).2 ⟨Finset.mem_coe.2 hi, hne⟩, hi⟩

/-- The walk invariant: the current vertex is reached from `x` by travelling in the *new* union
to a boundary vertex and then inside a **single** part of the *old* family. -/
def Good (S S' : ι → Finset (Sym2 V)) (Bd : Finset V) (x v : V) : Prop :=
  ∃ b ∈ Bd, (ofEdges (univ.biUnion S')).Reachable x b ∧
    (b = v ∨ ∃ i, (ofEdges (S i)).Reachable b v)

lemma good_step {S S' : ι → Finset (Sym2 V)} {Bd : Finset V}
    (hsame : ∀ i, ∀ p ∈ Bd, ∀ q ∈ Bd,
      (ofEdges (S i)).Reachable p q → (ofEdges (S' i)).Reachable p q)
    (hsupp : ∀ i, ∀ e ∈ S i, ∀ v ∈ e, v ∉ Bd → ∀ j, j ≠ i → ∀ f ∈ S j, v ∉ f)
    {x u v : V} (hu : Good S S' Bd x u)
    (hadj : (ofEdges (univ.biUnion S)).Adj u v) : Good S S' Bd x v := by
  obtain ⟨b, hbB, hxb, hbu⟩ := hu
  obtain ⟨i, hadji, hi⟩ := adj_union_part hadj
  by_cases huB : u ∈ Bd
  · refine ⟨u, huB, ?_, Or.inr ⟨i, hadji.reachable⟩⟩
    rcases hbu with rfl | ⟨j, hj⟩
    · exact hxb
    · exact hxb.trans (reachable_union S' j (hsame j b hbB u huB hj))
  · rcases hbu with rfl | ⟨j, hj⟩
    · exact absurd hbB huB
    · have hbne : b ≠ u := by rintro rfl; exact huB hbB
      have hji : j = i := by
        by_contra hjne
        obtain ⟨f, hf, huf⟩ := exists_edge_of_reachable_ne hj hbne
        exact hsupp i s(u, v) hi u (by simp) huB j hjne f hf huf
      have hj' : (ofEdges (S i)).Reachable b u := by rw [← hji]; exact hj
      exact ⟨b, hbB, hxb, Or.inr ⟨i, hj'.trans hadji.reachable⟩⟩

lemma good_transport {S S' : ι → Finset (Sym2 V)} {Bd : Finset V}
    (hsame : ∀ i, ∀ p ∈ Bd, ∀ q ∈ Bd,
      (ofEdges (S i)).Reachable p q → (ofEdges (S' i)).Reachable p q)
    (hsupp : ∀ i, ∀ e ∈ S i, ∀ v ∈ e, v ∉ Bd → ∀ j, j ≠ i → ∀ f ∈ S j, v ∉ f)
    {x u v : V} (W : (ofEdges (univ.biUnion S)).Walk u v) :
    Good S S' Bd x u → Good S S' Bd x v := by
  induction W with
  | nil => exact id
  | cons hadj _ ih => exact fun h => ih (good_step hsame hsupp h hadj)

lemma bc_reachable_of_reachable {S S' : ι → Finset (Sym2 V)} {Bd : Finset V}
    (hsame : ∀ i, ∀ p ∈ Bd, ∀ q ∈ Bd,
      (ofEdges (S i)).Reachable p q → (ofEdges (S' i)).Reachable p q)
    (hsupp : ∀ i, ∀ e ∈ S i, ∀ v ∈ e, v ∉ Bd → ∀ j, j ≠ i → ∀ f ∈ S j, v ∉ f)
    {x y : V} (hx : x ∈ Bd) (hy : y ∈ Bd)
    (h : (ofEdges (univ.biUnion S)).Reachable x y) :
    (ofEdges (univ.biUnion S')).Reachable x y := by
  obtain ⟨W⟩ := h
  obtain ⟨b, hbB, hxb, hby⟩ :=
    good_transport hsame hsupp W ⟨x, hx, SimpleGraph.Reachable.refl x, Or.inl rfl⟩
  rcases hby with rfl | ⟨j, hj⟩
  · exact hxb
  · exact hxb.trans (reachable_union S' j (hsame j b hbB y hy hj))

/-- **Connectivity depends only on the boundary partitions.** -/
theorem bc_boundary_congr (S S' : ι → Finset (Sym2 V)) (Bd : Finset V)
    (hsame : ∀ i, ∀ p ∈ Bd, ∀ q ∈ Bd,
      ((ofEdges (S i)).Reachable p q ↔ (ofEdges (S' i)).Reachable p q))
    (hsupp : ∀ i, ∀ e ∈ S i, ∀ v ∈ e, v ∉ Bd → ∀ j, j ≠ i → ∀ f ∈ S j, v ∉ f)
    (hsupp' : ∀ i, ∀ e ∈ S' i, ∀ v ∈ e, v ∉ Bd → ∀ j, j ≠ i → ∀ f ∈ S' j, v ∉ f)
    (x y : V) (hx : x ∈ Bd) (hy : y ∈ Bd) :
    ((ofEdges (Finset.univ.biUnion S)).Reachable x y
      ↔ (ofEdges (Finset.univ.biUnion S')).Reachable x y) :=
  ⟨bc_reachable_of_reachable (fun i p hp q hq => (hsame i p hp q hq).1) hsupp hx hy,
   bc_reachable_of_reachable (fun i p hp q hq => (hsame i p hp q hq).2) hsupp' hx hy⟩

end Boundary

/-! ## The canonical WZ edge sets (copies of the accepted `BunkbedAux.wzEdges_*`) -/

section WZStates

variable {V : Type*} [DecidableEq V]

theorem edges_support (a b c : V) (l : Fin 2) (s : WZ) (e : Sym2 (V × Fin 2))
    (he : e ∈ WZ.edges s (a, b, c) l) (v : V × Fin 2) (hv : v ∈ e) :
    v = (a, l) ∨ v = (b, l) ∨ v = (c, l) := by
  cases s <;>
    simp only [WZ.edges, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty] at he
  · rcases he with rfl | rfl | rfl <;> (simp only [Sym2.mem_iff] at hv; tauto)
  · subst he; simp only [Sym2.mem_iff] at hv; tauto
  · subst he; simp only [Sym2.mem_iff] at hv; tauto
  · subst he; simp only [Sym2.mem_iff] at hv; tauto

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
  · refine ⟨?_, ?_, ?_⟩
    · exact iff_of_true (reachable_of_mem (by simp [WZ.edges]) hab') (Or.inl rfl)
    · exact iff_of_true (reachable_of_mem (by simp [WZ.edges]) hbc') (Or.inl rfl)
    · exact iff_of_true (reachable_of_mem (by simp [WZ.edges]) hac') (Or.inl rfl)
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

end WZStates

/-! ## Facts about Hollom's hypergraph and the substituted graph -/

lemma fin2_cases : ∀ l : Fin 2, l = 0 ∨ l = 1 := by decide

lemma tr_ne_path : ∀ (i : Fin 6) (j : Fin 7), hollomTr i ≠ hollomPath j := by decide

lemma cs_ne_succ : ∀ i : Fin 6, hollomPath i.castSucc ≠ hollomPath i.succ := by decide

lemma hollomTriple_eq : ∀ i : Fin 6,
    hollomTriple i = (hollomTr i, hollomPath i.castSucc, hollomPath i.succ) := by decide

lemma iota_inj : Function.Injective iota := by
  intro a b h
  have hv : (iota a).val = (iota b).val := by rw [h]
  exact Fin.ext hv

lemma iota_val (v : Fin 10) : (iota v).val = v.val := rfl

lemma emb_val (i : Fin 6) (k : Fin 1205) : (emb i k).val = embN i k.val := rfl

lemma embN_zero (i : Fin 6) : embN i 0 = (hollomTr i).val := by simp [embN]
lemma embN_one (i : Fin 6) : embN i 1 = (hollomPath i.castSucc).val := by simp [embN]
lemma embN_last (i : Fin 6) : embN i 1204 = (hollomPath i.succ).val := by simp [embN]

lemma embN_interior (i : Fin 6) (k : ℕ) (h2 : 2 ≤ k) (h3 : k ≤ 1203) :
    embN i k = 10 + 1202 * i.val + (k - 2) := by
  unfold embN; split_ifs <;> omega

lemma embN_bdry (i : Fin 6) (k : ℕ) (h : k = 0 ∨ k = 1 ∨ k = 1204) : embN i k < 10 := by
  have h3 : (hollomTr i).val < 10 := (hollomTr i).isLt
  have h4 : (hollomPath i.castSucc).val < 10 := (hollomPath i.castSucc).isLt
  have h5 : (hollomPath i.succ).val < 10 := (hollomPath i.succ).isLt
  rcases h with rfl | rfl | rfl <;> (unfold embN; split_ifs <;> omega)

lemma one_val : (1 : Fin 1205).val = 1 := rfl
lemma last_val : (1204 : Fin 1205).val = 1204 := rfl

lemma emb_zero (i : Fin 6) : emb i 0 = iota (hollomTr i) :=
  Fin.ext (by rw [emb_val, iota_val]; exact embN_zero i)

lemma emb_one (i : Fin 6) : emb i 1 = iota (hollomPath i.castSucc) :=
  Fin.ext (by rw [emb_val, iota_val, one_val]; exact embN_one i)

lemma emb_last (i : Fin 6) : emb i 1204 = iota (hollomPath i.succ) :=
  Fin.ext (by rw [emb_val, iota_val, last_val]; exact embN_last i)

lemma idx_cases (k : Fin 1205) :
    k.val = 0 ∨ k.val = 1 ∨ k.val = 1204 ∨ (2 ≤ k.val ∧ k.val ≤ 1203) := by
  have := k.isLt; omega

lemma emb_val_eq {i j : Fin 6} {k l : Fin 1205} (h : emb i k = emb j l) :
    embN i k.val = embN j l.val := by
  rw [← emb_val i k, ← emb_val j l, h]

/-- An interior index pins down the copy *and* the index. -/
lemma emb_eq_block {i j : Fin 6} {k l : Fin 1205}
    (hk : 2 ≤ k.val) (hk' : k.val ≤ 1203) (h : emb i k = emb j l) : i = j ∧ k = l := by
  have hv : embN i k.val = embN j l.val := emb_val_eq h
  have h2 : embN i k.val = 10 + 1202 * i.val + (k.val - 2) := embN_interior i k.val hk hk'
  have hi6 : i.val < 6 := i.isLt
  have hj6 : j.val < 6 := j.isLt
  have hl : 2 ≤ l.val ∧ l.val ≤ 1203 := by
    rcases idx_cases l with hl | hl | hl | hl
    · have := embN_bdry j l.val (by omega); omega
    · have := embN_bdry j l.val (by omega); omega
    · have := embN_bdry j l.val (by omega); omega
    · exact hl
  have h3 : embN j l.val = 10 + 1202 * j.val + (l.val - 2) := embN_interior j l.val hl.1 hl.2
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

/-- A gadget index whose image is a hypergraph vertex is an attachment index. -/
lemma bdry_idx (i : Fin 6) (k : Fin 1205) (h : (emb i k).val < 10) :
    k = 0 ∨ k = 1 ∨ k = 1204 := by
  have hv : (emb i k).val = embN i k.val := rfl
  rcases idx_cases k with hk | hk | hk | hk
  · exact Or.inl (Fin.ext (by rw [hk]; rfl))
  · exact Or.inr (Or.inl (Fin.ext (by rw [hk, one_val])))
  · exact Or.inr (Or.inr (Fin.ext (by rw [hk, last_val])))
  · exfalso
    have h2 : embN i k.val = 10 + 1202 * i.val + (k.val - 2) := embN_interior i k.val hk.1 hk.2
    omega

/-- A gadget index whose image is not a hypergraph vertex is interior. -/
lemma nonbdry_interior (i : Fin 6) (k : Fin 1205) (h : ¬ (emb i k).val < 10) :
    2 ≤ k.val ∧ k.val ≤ 1203 := by
  rcases idx_cases k with hk | hk | hk | hk
  · exact absurd (show (emb i k).val < 10 from embN_bdry i k.val (Or.inl hk)) h
  · exact absurd (show (emb i k).val < 10 from embN_bdry i k.val (Or.inr (Or.inl hk))) h
  · exact absurd (show (emb i k).val < 10 from embN_bdry i k.val (Or.inr (Or.inr hk))) h
  · exact hk

/-! ## The two families of parts, on the common vertex type `Fin 7222 × Fin 2` -/

/-- The index type of the parts: six copies on each of the two levels, plus the posts. -/
abbrev Idx : Type := Fin 6 × Fin 2 ⊕ Unit

/-- The lift of the ten hypergraph vertices to the bunkbed over the substituted graph. -/
def gmap (p : Fin 10 × Fin 2) : Fin 7222 × Fin 2 := (iota p.1, p.2)

lemma gmap_inj : Function.Injective gmap := by
  rintro ⟨a, l⟩ ⟨b, m⟩ h
  simp only [gmap, Prod.mk.injEq] at h
  rw [iota_inj h.1, h.2]

/-- The boundary: the ten lifted hypergraph vertices on each of the two levels. -/
def bdryB : Finset (Fin 7222 × Fin 2) := Finset.univ.image gmap

lemma mem_bdryB {w : Fin 7222 × Fin 2} : w ∈ bdryB ↔ w.1.val < 10 := by
  constructor
  · intro hw
    obtain ⟨p, -, hp⟩ := Finset.mem_image.1 hw
    rw [← hp]
    exact p.1.isLt
  · intro hw
    exact Finset.mem_image.2 ⟨(⟨w.1.val, hw⟩, w.2), Finset.mem_univ _, rfl⟩

/-- The posts over the substituted transversal set, as a single part. -/
def postPart : Finset (Sym2 (Fin 7222 × Fin 2)) := subT.image (fun x => s((x, 0), (x, 1)))

lemma postPart_bdry : ∀ e ∈ postPart, ∀ v : Fin 7222 × Fin 2, v ∈ e → v ∈ bdryB := by
  intro e he v hv
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 he
  have ht' : t ∈ hollomT.image iota := ht
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 ht'
  rw [Sym2.mem_iff] at hv
  rcases hv with rfl | rfl <;> exact mem_bdryB.2 u.isLt

/-- The parts of the bunkbed graph: copy `i` on level `l`, plus the posts. -/
def bbFam (S₀ S₁ : Fin 6 → Finset (Sym2 (Fin 7222))) : Idx → Finset (Sym2 (Fin 7222 × Fin 2)) :=
  Sum.elim (fun p => (if p.2 = 0 then S₀ p.1 else S₁ p.1).image (liftLvl p.2))
    (fun _ => postPart)

/-- The parts of the Wierman-Ziff graph, transported along `iota`. -/
def wzFam (ψ : Fin 6 × Fin 2 → WZ) : Idx → Finset (Sym2 (Fin 7222 × Fin 2)) :=
  Sum.elim (fun p => (ψ p).edges
      (iota (hollomTr p.1), iota (hollomPath p.1.castSucc), iota (hollomPath p.1.succ)) p.2)
    (fun _ => postPart)

lemma bbFam_inl (S₀ S₁ : Fin 6 → Finset (Sym2 (Fin 7222))) (i : Fin 6) (l : Fin 2) :
    bbFam S₀ S₁ (Sum.inl (i, l)) = (if l = 0 then S₀ i else S₁ i).image (liftLvl l) := rfl

lemma wzFam_inl (ψ : Fin 6 × Fin 2 → WZ) (i : Fin 6) (l : Fin 2) :
    wzFam ψ (Sum.inl (i, l)) = (ψ (i, l)).edges
      (iota (hollomTr i), iota (hollomPath i.castSucc), iota (hollomPath i.succ)) l := rfl

/-! ## Decomposing the two edge sets as `biUnion`s over `Idx` -/

lemma biUnion_sum {V' κ : Type*} [DecidableEq V'] [Fintype κ] [DecidableEq κ]
    (F : κ → Finset V') (P : Finset V') :
    Finset.univ.biUnion (Sum.elim F (fun _ : Unit => P)) = Finset.univ.biUnion F ∪ P := by
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union, Sum.exists,
    Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro (⟨i, h⟩ | ⟨u, h⟩)
    · exact Or.inl ⟨i, h⟩
    · exact Or.inr h
  · rintro (⟨i, h⟩ | h)
    · exact Or.inl ⟨i, h⟩
    · exact Or.inr ⟨(), h⟩

lemma biUnion_fin2 {V' κ : Type*} [DecidableEq V'] [Fintype κ] [DecidableEq κ]
    (F : κ × Fin 2 → Finset V') :
    Finset.univ.biUnion F
      = Finset.univ.biUnion (fun i => F (i, 0)) ∪ Finset.univ.biUnion (fun i => F (i, 1)) := by
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union, Prod.exists]
  constructor
  · rintro ⟨i, l, h⟩
    rcases fin2_cases l with rfl | rfl
    · exact Or.inl ⟨i, h⟩
    · exact Or.inr ⟨i, h⟩
  · rintro (⟨i, h⟩ | ⟨i, h⟩)
    · exact ⟨i, 0, h⟩
    · exact ⟨i, 1, h⟩

lemma bbFam_biUnion (S₀ S₁ : Fin 6 → Finset (Sym2 (Fin 7222))) :
    Finset.univ.biUnion (bbFam S₀ S₁)
      = (Finset.univ.biUnion S₀).image (liftLvl 0) ∪ (Finset.univ.biUnion S₁).image (liftLvl 1)
        ∪ postPart := by
  have h1 : Finset.univ.biUnion (bbFam S₀ S₁)
      = Finset.univ.biUnion (fun p : Fin 6 × Fin 2 =>
          (if p.2 = 0 then S₀ p.1 else S₁ p.1).image (liftLvl p.2)) ∪ postPart :=
    biUnion_sum _ _
  rw [h1]
  congr 1
  rw [biUnion_fin2 (fun p : Fin 6 × Fin 2 => (if p.2 = 0 then S₀ p.1 else S₁ p.1).image
    (liftLvl p.2)), Finset.biUnion_image, Finset.biUnion_image]
  simp

lemma edges_transport (s : WZ) (i : Fin 6) (l : Fin 2) :
    (s.edges (hollomTriple i) l).image (Sym2.map gmap)
      = s.edges (iota (hollomTr i), iota (hollomPath i.castSucc), iota (hollomPath i.succ)) l := by
  rw [hollomTriple_eq i]
  cases s <;> simp [WZ.edges, gmap]

lemma postPart_transport :
    (posts hollomT).image (Sym2.map gmap) = postPart := by
  simp only [postPart, posts, subT, Finset.image_image]
  refine Finset.image_congr ?_
  intro t _
  simp [gmap]

/-- The edge set of the Wierman-Ziff graph on `Fin 10 × Fin 2`. -/
def wzE (ψ : Fin 6 × Fin 2 → WZ) : Finset (Sym2 (Fin 10 × Fin 2)) :=
  (Finset.univ.biUnion (fun p : Fin 6 × Fin 2 => (ψ p).edges (hollomTriple p.1) p.2))
    ∪ posts hollomT

lemma wzFam_biUnion (ψ : Fin 6 × Fin 2 → WZ) :
    Finset.univ.biUnion (wzFam ψ) = (wzE ψ).image (Sym2.map gmap) := by
  have h1 : Finset.univ.biUnion (wzFam ψ)
      = Finset.univ.biUnion (fun p : Fin 6 × Fin 2 => (ψ p).edges
          (iota (hollomTr p.1), iota (hollomPath p.1.castSucc), iota (hollomPath p.1.succ)) p.2)
        ∪ postPart := biUnion_sum _ _
  have h2 : (wzE ψ).image (Sym2.map gmap)
      = Finset.univ.biUnion (fun p : Fin 6 × Fin 2 =>
          ((ψ p).edges (hollomTriple p.1) p.2).image (Sym2.map gmap))
        ∪ (posts hollomT).image (Sym2.map gmap) := by
    simp only [wzE, Finset.image_union, Finset.biUnion_image]
  rw [h1, h2, postPart_transport]
  congr 1
  refine Finset.biUnion_congr rfl (fun p _ => ?_)
  exact (edges_transport (ψ p) p.1 p.2).symm

/-! ## Support of the parts -/

lemma bb_part_support (i : Fin 6) (l : Fin 2) (E : Finset (Sym2 (Fin 7222)))
    (hE : E ⊆ (gadgetE 1204).image (Sym2.map (emb i))) :
    ∀ e ∈ E.image (liftLvl l), ∀ v : Fin 7222 × Fin 2, v ∈ e →
      ∃ k : Fin 1205, v = (emb i k, l) := by
  intro e he v hv
  obtain ⟨e', he', rfl⟩ := Finset.mem_image.1 he
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 (hE he')
  have hmm : liftLvl l (Sym2.map (emb i) g)
      = Sym2.map (fun k : Fin 1205 => (emb i k, l)) g := by
    simp [liftLvl, Sym2.map_map, Function.comp]
  rw [hmm] at hv
  obtain ⟨k, -, hk⟩ := Sym2.mem_map.1 hv
  exact ⟨k, hk.symm⟩

/-! ## The parts agree on the boundary -/

/-- **The heart of the argument.**  On the boundary, a lifted copy of the gadget induces exactly
the reachability relation of the canonical edge set of the state `ψ (i, l)`. -/
lemma hsame_part (S₀ S₁ : Fin 6 → Finset (Sym2 (Fin 7222))) (ψ : Fin 6 × Fin 2 → WZ)
    (hsubL : ∀ (i : Fin 6) (l : Fin 2),
      (if l = 0 then S₀ i else S₁ i) ⊆ (gadgetE 1204).image (Sym2.map (emb i)))
    (hmatch : ∀ (i : Fin 6) (l : Fin 2),
        ((ofEdges (if l = 0 then S₀ i else S₁ i)).Reachable (emb i 0) (emb i 1)
            ↔ (ψ (i, l) = WZ.abc ∨ ψ (i, l) = WZ.ab_c))
      ∧ ((ofEdges (if l = 0 then S₀ i else S₁ i)).Reachable (emb i 1) (emb i 1204)
            ↔ (ψ (i, l) = WZ.abc ∨ ψ (i, l) = WZ.a_bc))
      ∧ ((ofEdges (if l = 0 then S₀ i else S₁ i)).Reachable (emb i 0) (emb i 1204)
            ↔ (ψ (i, l) = WZ.abc ∨ ψ (i, l) = WZ.ac_b)))
    (i : Fin 6) (l : Fin 2) (p : Fin 7222 × Fin 2) (hp : p ∈ bdryB)
    (q : Fin 7222 × Fin 2) (hq : q ∈ bdryB) :
    ((ofEdges (bbFam S₀ S₁ (Sum.inl (i, l)))).Reachable p q
      ↔ (ofEdges (wzFam ψ (Sum.inl (i, l)))).Reachable p q) := by
  rw [bbFam_inl, wzFam_inl]
  obtain ⟨m1, m2, m3⟩ := hmatch i l
  -- lift reachability inside the copy up to level `l`
  have hinj : Function.Injective (fun w : Fin 7222 => (w, l)) := fun a b h => congrArg Prod.fst h
  have himg : (if l = 0 then S₀ i else S₁ i).image (liftLvl l)
      = (if l = 0 then S₀ i else S₁ i).image (Sym2.map (fun w : Fin 7222 => (w, l))) := rfl
  have hlift : ∀ u v : Fin 1205,
      (ofEdges ((if l = 0 then S₀ i else S₁ i).image (liftLvl l))).Reachable
          (emb i u, l) (emb i v, l)
        ↔ (ofEdges (if l = 0 then S₀ i else S₁ i)).Reachable (emb i u) (emb i v) := by
    intro u v
    rw [himg]
    exact reach_map_iff hinj _ (emb i u) (emb i v)
  have L1 := (hlift 0 1).trans m1
  have L2 := (hlift 1 1204).trans m2
  have L3 := (hlift 0 1204).trans m3
  rw [emb_zero, emb_one] at L1
  rw [emb_one, emb_last] at L2
  rw [emb_zero, emb_last] at L3
  -- the three attachment vertices are distinct
  have hab : iota (hollomTr i) ≠ iota (hollomPath i.castSucc) := fun h =>
    tr_ne_path i i.castSucc (iota_inj h)
  have hbc : iota (hollomPath i.castSucc) ≠ iota (hollomPath i.succ) := fun h =>
    cs_ne_succ i (iota_inj h)
  have hac : iota (hollomTr i) ≠ iota (hollomPath i.succ) := fun h =>
    tr_ne_path i i.succ (iota_inj h)
  obtain ⟨R1, R2, R3⟩ := reach_iff (iota (hollomTr i)) (iota (hollomPath i.castSucc))
    (iota (hollomPath i.succ)) hab hbc hac l (ψ (i, l))
  have I1 := L1.trans R1.symm
  have I2 := L2.trans R2.symm
  have I3 := L3.trans R3.symm
  -- both parts touch the boundary only in the three attachment vertices
  have hLsup : ∀ w : Fin 7222 × Fin 2, w ∈ bdryB →
      (∃ e ∈ (if l = 0 then S₀ i else S₁ i).image (liftLvl l), w ∈ e) →
      (w = (iota (hollomTr i), l) ∨ w = (iota (hollomPath i.castSucc), l)
        ∨ w = (iota (hollomPath i.succ), l)) := by
    intro w hw hex
    obtain ⟨e, he, hwe⟩ := hex
    obtain ⟨k, rfl⟩ := bb_part_support i l _ (hsubL i l) e he w hwe
    have hk10 : (emb i k).val < 10 := mem_bdryB.1 hw
    rcases bdry_idx i k hk10 with rfl | rfl | rfl
    · exact Or.inl (by rw [emb_zero])
    · exact Or.inr (Or.inl (by rw [emb_one]))
    · exact Or.inr (Or.inr (by rw [emb_last]))
  have hRsup : ∀ w : Fin 7222 × Fin 2,
      (∃ e ∈ WZ.edges (ψ (i, l))
          (iota (hollomTr i), iota (hollomPath i.castSucc), iota (hollomPath i.succ)) l, w ∈ e) →
      (w = (iota (hollomTr i), l) ∨ w = (iota (hollomPath i.castSucc), l)
        ∨ w = (iota (hollomPath i.succ), l)) := by
    intro w hex
    obtain ⟨e, he, hwe⟩ := hex
    exact edges_support _ _ _ l (ψ (i, l)) e he w hwe
  -- the nine cases
  have pair : ∀ u v : Fin 7222 × Fin 2,
      (u = (iota (hollomTr i), l) ∨ u = (iota (hollomPath i.castSucc), l)
        ∨ u = (iota (hollomPath i.succ), l)) →
      (v = (iota (hollomTr i), l) ∨ v = (iota (hollomPath i.castSucc), l)
        ∨ v = (iota (hollomPath i.succ), l)) →
      ((ofEdges ((if l = 0 then S₀ i else S₁ i).image (liftLvl l))).Reachable u v
        ↔ (ofEdges (WZ.edges (ψ (i, l))
            (iota (hollomTr i), iota (hollomPath i.castSucc), iota (hollomPath i.succ))
              l)).Reachable u v) := by
    intro u v hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact iff_of_true (Reachable.refl _) (Reachable.refl _)
    · exact I1
    · exact I3
    · exact flipIff I1
    · exact iff_of_true (Reachable.refl _) (Reachable.refl _)
    · exact I2
    · exact flipIff I3
    · exact flipIff I2
    · exact iff_of_true (Reachable.refl _) (Reachable.refl _)
  by_cases hpq : p = q
  · subst hpq
    exact iff_of_true (Reachable.refl _) (Reachable.refl _)
  · constructor
    · intro h
      exact (pair p q (hLsup p hp (exists_edge_of_reachable_ne h.symm (Ne.symm hpq)))
        (hLsup q hq (exists_edge_of_reachable_ne h hpq))).1 h
    · intro h
      exact (pair p q (hRsup p (exists_edge_of_reachable_ne h.symm (Ne.symm hpq)))
        (hRsup q (exists_edge_of_reachable_ne h hpq))).2 h

/-! ## Interior vertices are private to their part -/

lemma hsupp_bb (S₀ S₁ : Fin 6 → Finset (Sym2 (Fin 7222)))
    (hsubL : ∀ (i : Fin 6) (l : Fin 2),
      (if l = 0 then S₀ i else S₁ i) ⊆ (gadgetE 1204).image (Sym2.map (emb i))) :
    ∀ z : Idx, ∀ e ∈ bbFam S₀ S₁ z, ∀ v ∈ e, v ∉ bdryB →
      ∀ z', z' ≠ z → ∀ f ∈ bbFam S₀ S₁ z', v ∉ f := by
  intro z
  rcases z with ⟨i, l⟩ | u
  · intro e he v hv hvB z' hz' f hf hvf
    rw [bbFam_inl] at he
    obtain ⟨k, rfl⟩ := bb_part_support i l _ (hsubL i l) e he v hv
    have hint := nonbdry_interior i k (fun hlt => hvB (mem_bdryB.2 hlt))
    rcases z' with ⟨j, l'⟩ | u'
    · rw [bbFam_inl] at hf
      obtain ⟨k', hk'⟩ := bb_part_support j l' _ (hsubL j l') f hf _ hvf
      have h1 : emb i k = emb j k' := congrArg Prod.fst hk'
      have h2 : l = l' := congrArg Prod.snd hk'
      obtain ⟨hij, -⟩ := emb_eq_block hint.1 hint.2 h1
      exact hz' (by rw [← hij, ← h2])
    · exact hvB (postPart_bdry f hf _ hvf)
  · intro e he v hv hvB
    exact absurd (postPart_bdry e he v hv) hvB

lemma hsupp_wz (ψ : Fin 6 × Fin 2 → WZ) :
    ∀ z : Idx, ∀ e ∈ wzFam ψ z, ∀ v ∈ e, v ∉ bdryB →
      ∀ z', z' ≠ z → ∀ f ∈ wzFam ψ z', v ∉ f := by
  intro z
  rcases z with ⟨i, l⟩ | u
  · intro e he v hv hvB
    rw [wzFam_inl] at he
    rcases edges_support _ _ _ l (ψ (i, l)) e he v hv with rfl | rfl | rfl
    · exact absurd (mem_bdryB.2 (hollomTr i).isLt) hvB
    · exact absurd (mem_bdryB.2 (hollomPath i.castSucc).isLt) hvB
    · exact absurd (mem_bdryB.2 (hollomPath i.succ).isLt) hvB
  · intro e he v hv hvB
    exact absurd (postPart_bdry e he v hv) hvB

end Bunkbed.Sub3

/-! ## The requested statement -/

open Bunkbed Bunkbed.Hyper Bunkbed.Sub3 SimpleGraph Finset

/-- **Bunkbed reachability depends only on the per-copy boundary partitions.**

If, for every copy `i` and every level `l`, the open edges of that copy on that level connect its
three attachment vertices `emb i 0`, `emb i 1`, `emb i 1204` exactly as the Wierman-Ziff state
`ψ (i, l)` prescribes, then reachability between lifted hypergraph vertices in the bunkbed graph
over the substituted graph agrees with reachability in the Wierman-Ziff graph. -/
theorem solution (S₀ S₁ : Fin 6 → Finset (Sym2 (Fin 7222)))
    (hsub : ∀ i, S₀ i ⊆ (gadgetE 1204).image (Sym2.map (Bunkbed.Sub.emb i)))
    (hsub' : ∀ i, S₁ i ⊆ (gadgetE 1204).image (Sym2.map (Bunkbed.Sub.emb i)))
    (ψ : Fin 6 × Fin 2 → WZ)
    (hmatch : ∀ (i : Fin 6) (l : Fin 2),
        ((ofEdges (if l = 0 then S₀ i else S₁ i)).Reachable
              (Bunkbed.Sub.emb i 0) (Bunkbed.Sub.emb i 1)
            ↔ (ψ (i, l) = WZ.abc ∨ ψ (i, l) = WZ.ab_c))
      ∧ ((ofEdges (if l = 0 then S₀ i else S₁ i)).Reachable
              (Bunkbed.Sub.emb i 1) (Bunkbed.Sub.emb i 1204)
            ↔ (ψ (i, l) = WZ.abc ∨ ψ (i, l) = WZ.a_bc))
      ∧ ((ofEdges (if l = 0 then S₀ i else S₁ i)).Reachable
              (Bunkbed.Sub.emb i 0) (Bunkbed.Sub.emb i 1204)
            ↔ (ψ (i, l) = WZ.abc ∨ ψ (i, l) = WZ.ac_b)))
    (x y : Fin 10) (l : Fin 2) :
    (bbGraph Bunkbed.Sub.subT (Finset.univ.biUnion S₀) (Finset.univ.biUnion S₁)).Reachable
        (Bunkbed.Sub.iota x, 0) (Bunkbed.Sub.iota y, l)
      ↔ (wzGraph hollomTriple hollomT ψ).Reachable (x, 0) (y, l) := by
  have hsubL : ∀ (i : Fin 6) (m : Fin 2),
      (if m = 0 then S₀ i else S₁ i) ⊆ (gadgetE 1204).image (Sym2.map (Bunkbed.Sub.emb i)) := by
    intro i m
    rcases fin2_cases m with rfl | rfl
    · simpa using hsub i
    · simpa using hsub' i
  have hx : ((Bunkbed.Sub.iota x, 0) : Fin 7222 × Fin 2) ∈ bdryB := mem_bdryB.2 x.isLt
  have hy : ((Bunkbed.Sub.iota y, l) : Fin 7222 × Fin 2) ∈ bdryB := mem_bdryB.2 y.isLt
  have e1 : bbGraph Bunkbed.Sub.subT (Finset.univ.biUnion S₀) (Finset.univ.biUnion S₁)
      = ofEdges (Finset.univ.biUnion (bbFam S₀ S₁)) := by
    rw [bbFam_biUnion]
    rfl
  have hsame : ∀ z : Idx, ∀ p ∈ bdryB, ∀ q ∈ bdryB,
      ((ofEdges (bbFam S₀ S₁ z)).Reachable p q ↔ (ofEdges (wzFam ψ z)).Reachable p q) := by
    intro z
    rcases z with ⟨i, m⟩ | u
    · exact fun p hp q hq => hsame_part S₀ S₁ ψ hsubL hmatch i m p hp q hq
    · exact fun _ _ _ _ => Iff.rfl
  have hcong := bc_boundary_congr (bbFam S₀ S₁) (wzFam ψ) bdryB hsame
    (hsupp_bb S₀ S₁ hsubL) (hsupp_wz ψ) (Bunkbed.Sub.iota x, 0) (Bunkbed.Sub.iota y, l) hx hy
  rw [e1, hcong, wzFam_biUnion]
  exact reach_map_iff gmap_inj (wzE ψ) (x, 0) (y, l)

/-! ## Sanity check: the hypotheses are satisfiable, so the theorem is not vacuous

With every gadget edge closed, every copy realises the state `a|b|c` on both levels, and the
theorem specialises to the (true) statement that the two sides agree.  This also checks that
level `0` of the bunkbed really is governed by `S₀`. -/

namespace Bunkbed.Sub3

open Bunkbed.Sub

lemma not_reach_empty {W : Type*} {u v : W} (h : u ≠ v) :
    ¬ (ofEdges (∅ : Finset (Sym2 W))).Reachable u v :=
  not_reachable_of_sep (K := {u}) (fun a b hab => absurd hab (by simp)) rfl
    (by simpa using h.symm)

lemma emb_zero_ne_one (i : Fin 6) : emb i 0 ≠ emb i 1 := by
  rw [emb_zero, emb_one]
  exact fun h => tr_ne_path i i.castSucc (iota_inj h)

lemma emb_one_ne_last (i : Fin 6) : emb i 1 ≠ emb i 1204 := by
  rw [emb_one, emb_last]
  exact fun h => cs_ne_succ i (iota_inj h)

lemma emb_zero_ne_last (i : Fin 6) : emb i 0 ≠ emb i 1204 := by
  rw [emb_zero, emb_last]
  exact fun h => tr_ne_path i i.succ (iota_inj h)

end Bunkbed.Sub3

example (x y : Fin 10) (l : Fin 2) :
    (bbGraph Bunkbed.Sub.subT
        (Finset.univ.biUnion (fun _ : Fin 6 => (∅ : Finset (Sym2 (Fin 7222)))))
        (Finset.univ.biUnion (fun _ : Fin 6 => (∅ : Finset (Sym2 (Fin 7222)))))).Reachable
        (Bunkbed.Sub.iota x, 0) (Bunkbed.Sub.iota y, l)
      ↔ (wzGraph hollomTriple hollomT (fun _ => WZ.a_b_c)).Reachable (x, 0) (y, l) := by
  refine solution _ _ (fun i => by simp) (fun i => by simp) _ (fun i m => ?_) x y l
  have hE : (if m = 0 then (∅ : Finset (Sym2 (Fin 7222))) else ∅) = ∅ := by
    rcases fin2_cases m with rfl | rfl <;> simp
  rw [hE]
  refine ⟨iff_of_false (not_reach_empty (emb_zero_ne_one i)) (by decide),
    iff_of_false (not_reach_empty (emb_one_ne_last i)) (by decide),
    iff_of_false (not_reach_empty (emb_zero_ne_last i)) (by decide)⟩

#print axioms Bunkbed.Sub3.reach_map_iff
#print axioms Bunkbed.Sub3.bc_boundary_congr
#print axioms Bunkbed.Sub3.hsame_part
#print axioms Bunkbed.Sub3.hsupp_bb
#print axioms Bunkbed.Sub3.hsupp_wz
#print axioms Bunkbed.Sub3.bbFam_biUnion
#print axioms Bunkbed.Sub3.wzFam_biUnion
#print axioms solution
