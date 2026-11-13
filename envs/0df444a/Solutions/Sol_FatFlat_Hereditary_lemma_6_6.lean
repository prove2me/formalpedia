-- Prove2me | solution 1 for FatFlat.Hereditary.lemma_6_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:17:53.171611+00:00
-- url     : https://prove2.me/submissions/bf6fda26-b85b-441c-92b3-153fc9a1a17e

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Classes
import Theorems.Thm_FatFlat_Hereditary_lemma_6_4

section
set_option autoImplicit false

namespace FatFlat.Dev.Emb
open SparseDisc

/-- subdivision with constant `k` -/
noncomputable abbrev SD {W : Type} (G : SimpleGraph W) (k : ℕ) :=
  SparseDisc.subdivide G (fun _ => k)

section adj
variable {W : Type} (G : SimpleGraph W) (k : ℕ)

lemma SD_adj_inl_inl (u v : W) : ¬ (SD G k).Adj (Sum.inl u) (Sum.inl v) := by
  simp [SD, SparseDisc.subdivide, SimpleGraph.fromRel_adj]

lemma SD_adj_inl_inr (u : W) (e : G.edgeSet) (i : Fin (k + 1)) :
    (SD G k).Adj (Sum.inl u) (Sum.inr ⟨e, i⟩) ↔
      (u = (Quot.out (e : Sym2 W)).1 ∧ i.val = 0) ∨ (u = (Quot.out (e : Sym2 W)).2 ∧ i.val = k) := by
  simp [SD, SparseDisc.subdivide, SimpleGraph.fromRel_adj]

lemma SD_adj_inr_inr (e e' : G.edgeSet) (i : Fin (k + 1)) (j : Fin (k + 1)) :
    (SD G k).Adj (Sum.inr ⟨e, i⟩) (Sum.inr ⟨e', j⟩) ↔
      e = e' ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  simp [SD, SparseDisc.subdivide, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact ⟨h.1, Or.inl h.2⟩
    · exact ⟨h.1.symm, Or.inr h.2⟩
  · rintro ⟨rfl, h⟩
    refine ⟨fun _ hij => ?_, ?_⟩
    · subst hij; omega
    · rcases h with h | h
      · exact Or.inl ⟨rfl, h⟩
      · exact Or.inr ⟨rfl, h⟩

lemma out_eq (e : Sym2 W) : s((Quot.out e).1, (Quot.out e).2) = e := Quot.out_eq e

open Classical in
/-- index of position `i` when the path of `e` is walked starting from `x` -/
noncomputable def pos (e : G.edgeSet) (x : W) (i : Fin (k + 1)) : Fin (k + 1) :=
  if (Quot.out (e : Sym2 W)).1 = x then i else Fin.rev i

lemma pos_inj (e : G.edgeSet) (x : W) (i j : Fin (k + 1)) :
    pos G k e x i = pos G k e x j ↔ i = j := by
  unfold pos
  split_ifs <;> simp

open Classical in
lemma pos_adj_inl (e : G.edgeSet) (x y : W) (hxy : (e : Sym2 W) = s(x, y)) (hne : x ≠ y)
    (u : W) (j : Fin (k + 1)) :
    (SD G k).Adj (Sum.inl u) (Sum.inr ⟨e, pos G k e x j⟩) ↔
      (u = x ∧ j.val = 0) ∨ (u = y ∧ j.val = k) := by
  rw [SD_adj_inl_inr]
  have h := out_eq (e : Sym2 W)
  have hpos : pos G k e x j = if (Quot.out (e : Sym2 W)).1 = x then j else Fin.rev j := rfl
  generalize (Quot.out (e : Sym2 W)).1 = a at h hpos ⊢
  generalize (Quot.out (e : Sym2 W)).2 = b at h hpos ⊢
  rw [hxy] at h
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [hpos, h1, h2]
  · have hb : ¬ a = x := fun h => hne (h.symm.trans h1)
    rw [hpos, if_neg hb]
    simp only [Fin.val_rev, h1, h2]
    constructor
    · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
      · right; exact ⟨h, by omega⟩
      · left; exact ⟨h, by omega⟩
    · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
      · right; exact ⟨h, by omega⟩
      · left; exact ⟨h, by omega⟩

lemma pos_adj_inr (e : G.edgeSet) (x : W) (i j : Fin (k + 1)) :
    (SD G k).Adj (Sum.inr ⟨e, pos G k e x i⟩) (Sum.inr ⟨e, pos G k e x j⟩) ↔
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  rw [SD_adj_inr_inr]
  unfold pos
  split_ifs <;> simp only [Fin.val_rev, true_and] <;> omega

end adj


section functor
variable {W W' : Type} {H : SimpleGraph W} {H' : SimpleGraph W'}

end functor

section web
open FatFlat.Hereditary

lemma webOf_adj {V : Type} (G : SimpleGraph V) (P : Set V) (x y : V) :
    (webOf G P).Adj x y ↔ G.Adj x y ∨ (x ≠ y ∧ ∃ p ∈ P, G.Adj p x ∧ G.Adj p y) := by
  simp only [webOf, SimpleGraph.sup_adj, SimpleGraph.fromRel_adj]
  apply or_congr Iff.rfl
  apply and_congr Iff.rfl
  constructor
  · rintro (⟨p, hp, h1, h2⟩ | ⟨p, hp, h1, h2⟩)
    · exact ⟨p, hp, h1, h2⟩
    · exact ⟨p, hp, h2, h1⟩
  · rintro ⟨p, hp, h1, h2⟩
    exact Or.inl ⟨p, hp, h1, h2⟩

/-- A graph embedding induces an embedding of webs when the new cliques correspond. -/
def webOfEmb {V V' : Type} {G : SimpleGraph V} {G' : SimpleGraph V'} (F : G ↪g G')
    (P : Set V) (P' : Set V') (h1 : ∀ p ∈ P, F p ∈ P')
    (h2 : ∀ p' ∈ P', ∀ x y, x ≠ y → G'.Adj p' (F x) → G'.Adj p' (F y) → (webOf G P).Adj x y) :
    webOf G P ↪g webOf G' P' where
  toFun := F
  inj' := F.injective
  map_rel_iff' := by
    intro x y
    rw [webOf_adj, webOf_adj]
    constructor
    · rintro (h | ⟨hne, p', hp', ha, hb⟩)
      · exact Or.inl (F.map_adj_iff.1 h)
      · have hxy : x ≠ y := fun h => hne (by simp [h])
        have := h2 p' hp' x y hxy ha hb
        rwa [webOf_adj] at this
    · rintro (h | ⟨hne, p, hp, ha, hb⟩)
      · exact Or.inl (F.map_adj_iff.2 h)
      · refine Or.inr ⟨fun h => hne (F.injective h), F p, h1 p hp, ?_, ?_⟩
        · exact F.map_adj_iff.2 ha
        · exact F.map_adj_iff.2 hb

variable {W W' : Type} {H : SimpleGraph W} {H' : SimpleGraph W'}

end web
end FatFlat.Dev.Emb
end

section
set_option autoImplicit false

namespace FatFlat.Dev.L66Pat
open FatFlat.Dev.Emb FatFlat.Hereditary

abbrev BG (n m : ℕ) : SimpleGraph (Fin n ⊕ Fin m) := completeBipartiteGraph (Fin n) (Fin m)

/-- coordinates: principal vertices and `(i, j, t)` path vertices -/
abbrev KT (n m k : ℕ) : Type := (Fin n ⊕ Fin m) ⊕ (Fin n × Fin m × Fin (k + 1))

def KR (n m k : ℕ) : KT n m k → KT n m k → Prop
  | Sum.inl (Sum.inl i), Sum.inr (i', _, t) => i = i' ∧ t.val = 0
  | Sum.inl (Sum.inr j), Sum.inr (_, j', t) => j = j' ∧ t.val = k
  | Sum.inr (i, j, t), Sum.inr (i', j', t') => i = i' ∧ j = j' ∧ t.val + 1 = t'.val
  | _, _ => False

def KG (n m k : ℕ) : SimpleGraph (KT n m k) := SimpleGraph.fromRel (KR n m k)

section kg
variable {n m k : ℕ}

lemma KG_inl_inl (u v : Fin n ⊕ Fin m) : ¬ (KG n m k).Adj (Sum.inl u) (Sum.inl v) := by
  simp [KG, SimpleGraph.fromRel_adj, KR]

lemma KG_inl_inr (u : Fin n ⊕ Fin m) (i : Fin n) (j : Fin m) (t : Fin (k + 1)) :
    (KG n m k).Adj (Sum.inl u) (Sum.inr (i, j, t)) ↔
      (u = Sum.inl i ∧ t.val = 0) ∨ (u = Sum.inr j ∧ t.val = k) := by
  rcases u with a | b <;> simp [KG, SimpleGraph.fromRel_adj, KR, eq_comm]

lemma KG_inr_inl (u : Fin n ⊕ Fin m) (i : Fin n) (j : Fin m) (t : Fin (k + 1)) :
    (KG n m k).Adj (Sum.inr (i, j, t)) (Sum.inl u) ↔
      (u = Sum.inl i ∧ t.val = 0) ∨ (u = Sum.inr j ∧ t.val = k) := by
  rw [SimpleGraph.adj_comm, KG_inl_inr]

lemma KG_inr_inr (i i' : Fin n) (j j' : Fin m) (t t' : Fin (k + 1)) :
    (KG n m k).Adj (Sum.inr (i, j, t)) (Sum.inr (i', j', t')) ↔
      i = i' ∧ j = j' ∧ (t.val + 1 = t'.val ∨ t'.val + 1 = t.val) := by
  simp only [KG, SimpleGraph.fromRel_adj, KR, ne_eq, Sum.inr.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨-, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩
    · exact ⟨h1, h2, Or.inl h3⟩
    · exact ⟨h1.symm, h2.symm, Or.inr h3⟩
  · rintro ⟨rfl, rfl, h⟩
    refine ⟨?_, ?_⟩
    · rintro ⟨-, -, rfl⟩; omega
    · rcases h with h | h
      · exact Or.inl ⟨rfl, rfl, h⟩
      · exact Or.inr ⟨rfl, rfl, h⟩

end kg

section psi
variable {n m k : ℕ}

def edgeOf (i : Fin n) (j : Fin m) : (BG n m).edgeSet :=
  ⟨s(Sum.inl i, Sum.inr j), by simp [completeBipartiteGraph_adj]⟩

lemma edge_cases (e : (BG n m).edgeSet) : ∃ p : Fin n × Fin m, e = edgeOf p.1 p.2 := by
  obtain ⟨s, hs⟩ := e
  induction s using Sym2.ind with
  | _ a b =>
    rcases a with i | j <;> rcases b with i' | j'
    · simp [completeBipartiteGraph_adj] at hs
    · exact ⟨(i, j'), rfl⟩
    · refine ⟨(i', j), ?_⟩
      apply Subtype.ext
      simp [edgeOf, Sym2.eq_swap]
    · simp [completeBipartiteGraph_adj] at hs

lemma edgeOf_inj {i i' : Fin n} {j j' : Fin m} (h : edgeOf i j = edgeOf i' j') : i = i' ∧ j = j' := by
  have := congrArg Subtype.val h
  simpa [edgeOf] using this

lemma pos_pos (G : SimpleGraph (Fin n ⊕ Fin m)) (e : G.edgeSet) (x : Fin n ⊕ Fin m)
    (t : Fin (k + 1)) : pos G k e x (pos G k e x t) = t := by
  unfold pos
  split_ifs <;> simp

noncomputable def psi (n m k : ℕ) : (Fin n ⊕ Fin m) ⊕ (Σ _ : (BG n m).edgeSet, Fin (k + 1)) → KT n m k
  | Sum.inl w => Sum.inl w
  | Sum.inr ⟨e, t⟩ =>
    Sum.inr ((Classical.choose (edge_cases e)).1, (Classical.choose (edge_cases e)).2,
      pos (BG n m) k e (Sum.inl (Classical.choose (edge_cases e)).1) t)

lemma psi_inr (i : Fin n) (j : Fin m) (t : Fin (k + 1)) :
    psi n m k (Sum.inr ⟨edgeOf i j, t⟩) =
      Sum.inr (i, j, pos (BG n m) k (edgeOf i j) (Sum.inl i) t) := by
  have h := Classical.choose_spec (edge_cases (edgeOf i j))
  have h2 := edgeOf_inj h
  simp only [psi]
  rw [← h2.1, ← h2.2]

lemma psi_adj (x y : (Fin n ⊕ Fin m) ⊕ (Σ _ : (BG n m).edgeSet, Fin (k + 1))) :
    (SD (BG n m) k).Adj x y ↔ (KG n m k).Adj (psi n m k x) (psi n m k y) := by
  have key : ∀ (i : Fin n) (j : Fin m) (u : Fin n ⊕ Fin m) (s : Fin (k + 1)),
      (SD (BG n m) k).Adj (Sum.inl u) (Sum.inr ⟨edgeOf i j, pos (BG n m) k (edgeOf i j) (Sum.inl i) s⟩) ↔
      (KG n m k).Adj (Sum.inl u) (Sum.inr (i, j, s)) := by
    intro i j u s
    rw [pos_adj_inl (BG n m) k (edgeOf i j) (Sum.inl i) (Sum.inr j) rfl (by simp), KG_inl_inr]
  rcases x with u | ⟨e, t⟩
  · rcases y with v | ⟨e', t'⟩
    · simp [psi, SD_adj_inl_inl, KG_inl_inl]
    · obtain ⟨⟨i, j⟩, rfl⟩ := edge_cases e'
      obtain ⟨s, rfl⟩ : ∃ s, t' = pos (BG n m) k (edgeOf i j) (Sum.inl i) s :=
        ⟨pos (BG n m) k (edgeOf i j) (Sum.inl i) t', (pos_pos _ _ _ _).symm⟩
      rw [psi_inr, pos_pos]
      simpa [psi] using key i j u s
  · obtain ⟨⟨i, j⟩, rfl⟩ := edge_cases e
    obtain ⟨s, rfl⟩ : ∃ s, t = pos (BG n m) k (edgeOf i j) (Sum.inl i) s :=
      ⟨pos (BG n m) k (edgeOf i j) (Sum.inl i) t, (pos_pos _ _ _ _).symm⟩
    rcases y with v | ⟨e', t'⟩
    · rw [SimpleGraph.adj_comm, SimpleGraph.adj_comm (KG n m k)]
      rw [psi_inr, pos_pos]
      simpa [psi] using key i j v s
    · obtain ⟨⟨i', j'⟩, rfl⟩ := edge_cases e'
      obtain ⟨s', rfl⟩ : ∃ s', t' = pos (BG n m) k (edgeOf i' j') (Sum.inl i') s' :=
        ⟨pos (BG n m) k (edgeOf i' j') (Sum.inl i') t', (pos_pos _ _ _ _).symm⟩
      rw [psi_inr, psi_inr, pos_pos, pos_pos, KG_inr_inr]
      by_cases h : (edgeOf i j : (BG n m).edgeSet) = edgeOf i' j'
      · obtain ⟨rfl, rfl⟩ := edgeOf_inj h
        rw [pos_adj_inr (BG n m) k (edgeOf i j) (Sum.inl i) s s']
        simp
      · rw [SD_adj_inr_inr]
        constructor
        · rintro ⟨hh, -⟩
          exact absurd hh h
        · rintro ⟨h1, h2, -⟩
          exact absurd (by simp only at h1 h2; rw [h1, h2]) h

lemma psi_inj : Function.Injective (psi n m k) := by
  rintro (u | ⟨e, t⟩) (v | ⟨e', t'⟩) h
  · simpa [psi] using h
  · rcases edge_cases e' with ⟨⟨i, j⟩, rfl⟩
    simp [psi, psi_inr] at h
  · rcases edge_cases e with ⟨⟨i, j⟩, rfl⟩
    simp [psi, psi_inr] at h
  · obtain ⟨⟨i, j⟩, rfl⟩ := edge_cases e
    obtain ⟨⟨i', j'⟩, rfl⟩ := edge_cases e'
    rw [psi_inr, psi_inr] at h
    simp only [Sum.inr.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, h3⟩ := h
    have := (pos_inj (BG n m) k (edgeOf i j) (Sum.inl i) t t').1 h3
    rw [this]

/-- the embedding of the subdivided biclique into the coordinate graph -/
noncomputable def psiEmb (n m k : ℕ) : SD (BG n m) k ↪g KG n m k where
  toFun := psi n m k
  inj' := psi_inj
  map_rel_iff' := fun {x y} => (psi_adj x y).symm

end psi

section webs
variable {n m k : ℕ}

/-- adjacency of the coordinate graph with the optional web cliques -/
def R (n m k : ℕ) (wa wb : Bool) (u v : KT n m k) : Prop :=
  (KG n m k).Adj u v ∨
  (wa = true ∧ u ≠ v ∧ ∃ (i : Fin n) (j j' : Fin m),
      u = Sum.inr (i, j, 0) ∧ v = Sum.inr (i, j', 0)) ∨
  (wb = true ∧ u ≠ v ∧ ∃ (i i' : Fin n) (j : Fin m),
      u = Sum.inr (i, j, Fin.last k) ∧ v = Sum.inr (i', j, Fin.last k))

lemma R_ff (u v : KT n m k) : R n m k false false u v ↔ (KG n m k).Adj u v := by
  simp [R]

lemma webBoth_adj (u v : KT n m k) :
    (webOf (KG n m k) (Set.range (Sum.inl : Fin n ⊕ Fin m → KT n m k))).Adj u v ↔
      R n m k true true u v := by
  rw [webOf_adj]
  unfold R
  apply or_congr Iff.rfl
  simp only [true_and]
  constructor
  · rintro ⟨hne, p, ⟨w, rfl⟩, h1, h2⟩
    rcases u with u | ⟨i, j, t⟩
    · exact absurd h1 (by simp [KG_inl_inl])
    rcases v with v | ⟨i', j', t'⟩
    · exact absurd h2 (by simp [KG_inl_inl])
    rw [KG_inl_inr] at h1 h2
    rcases h1 with ⟨rfl, ht⟩ | ⟨rfl, ht⟩ <;> rcases h2 with ⟨h2, ht'⟩ | ⟨h2, ht'⟩
    · simp only [Sum.inl.injEq] at h2
      subst h2
      left
      refine ⟨hne, i, j, j', ?_, ?_⟩ <;> simp [Fin.ext_iff, ht, ht']
    · simp at h2
    · simp at h2
    · simp only [Sum.inr.injEq] at h2
      subst h2
      right
      refine ⟨hne, i, i', j, ?_, ?_⟩ <;> simp [Fin.ext_iff, ht, ht']
  · rintro (⟨hne, i, j, j', rfl, rfl⟩ | ⟨hne, i, i', j, rfl, rfl⟩)
    · refine ⟨hne, Sum.inl (Sum.inl i), ⟨_, rfl⟩, ?_, ?_⟩ <;> simp [KG_inl_inr]
    · refine ⟨hne, Sum.inl (Sum.inr j), ⟨_, rfl⟩, ?_, ?_⟩ <;> simp [KG_inl_inr]

lemma webMix_adj (u v : KT n m k) :
    (webOf (KG n m k) (Set.range (fun i : Fin n => (Sum.inl (Sum.inl i) : KT n m k)))).Adj u v ↔
      R n m k true false u v := by
  rw [webOf_adj]
  unfold R
  apply or_congr Iff.rfl
  simp only [true_and, Bool.false_eq_true, false_and, or_false]
  constructor
  · rintro ⟨hne, p, ⟨w, rfl⟩, h1, h2⟩
    rcases u with u | ⟨i, j, t⟩
    · exact absurd h1 (by simp [KG_inl_inl])
    rcases v with v | ⟨i', j', t'⟩
    · exact absurd h2 (by simp [KG_inl_inl])
    rw [KG_inl_inr] at h1 h2
    rcases h1 with ⟨h1, ht⟩ | ⟨h1, ht⟩ <;> rcases h2 with ⟨h2, ht'⟩ | ⟨h2, ht'⟩
    · simp only [Sum.inl.injEq] at h1 h2
      subst h1 h2
      refine ⟨hne, w, j, j', ?_, ?_⟩ <;> simp [Fin.ext_iff, ht, ht']
    all_goals simp at h1 h2 ⊢
  · rintro ⟨hne, i, j, j', rfl, rfl⟩
    exact ⟨hne, Sum.inl (Sum.inl i), ⟨_, rfl⟩, by simp [KG_inl_inr], by simp [KG_inl_inr]⟩

/-- swapping the two sides -/
def swapT (m k : ℕ) : KT m m k → KT m m k
  | Sum.inl (Sum.inl i) => Sum.inl (Sum.inr i)
  | Sum.inl (Sum.inr j) => Sum.inl (Sum.inl j)
  | Sum.inr (i, j, t) => Sum.inr (j, i, Fin.rev t)

lemma swapT_swapT (u : KT m m k) : swapT m k (swapT m k u) = u := by
  rcases u with (a | a) | ⟨i, j, t⟩ <;> simp [swapT]

lemma KG_swap (u v : KT m m k) : (KG m m k).Adj (swapT m k u) (swapT m k v) ↔ (KG m m k).Adj u v := by
  rcases u with (a | a) | ⟨i, j, t⟩ <;> rcases v with (b | b) | ⟨i', j', t'⟩ <;>
    simp only [swapT, KG_inl_inl, KG_inl_inr, KG_inr_inl, KG_inr_inr, Fin.val_rev, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, false_and, or_false, false_or, and_false, iff_self] <;>
    first | omega | (constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h2.symm ▸ h1, h1.symm ▸ h2, by omega⟩) | skip

lemma swapT_eq_iff (u x : KT m m k) : swapT m k u = x ↔ u = swapT m k x := by
  constructor
  · rintro rfl; rw [swapT_swapT]
  · rintro rfl; rw [swapT_swapT]

lemma R_swap (wa wb : Bool) (u v : KT m m k) :
    R m m k wb wa (swapT m k u) (swapT m k v) ↔ R m m k wa wb u v := by
  have h1 : swapT m k u ≠ swapT m k v ↔ u ≠ v := by
    constructor
    · intro h e; exact h (by rw [e])
    · intro h e
      apply h
      have := congrArg (swapT m k) e
      rwa [swapT_swapT, swapT_swapT] at this
  unfold R
  rw [KG_swap, h1]
  apply or_congr Iff.rfl
  simp only [swapT_eq_iff]
  simp only [swapT, Fin.rev_zero, Fin.rev_last]
  constructor
  · rintro (⟨hb, hne, i, j, j', h, h'⟩ | ⟨ha, hne, i, i', j, h, h'⟩)
    · right; exact ⟨hb, hne, j, j', i, h, h'⟩
    · left; exact ⟨ha, hne, j, i, i', h, h'⟩
  · rintro (⟨ha, hne, i, j, j', h, h'⟩ | ⟨hb, hne, i, i', j, h, h'⟩)
    · right; exact ⟨ha, hne, j, j', i, h, h'⟩
    · left; exact ⟨hb, hne, j, i, i', h, h'⟩

lemma webSD_emb {V : Type} (G : SimpleGraph V) (P : Set ((Fin n ⊕ Fin m) ⊕ (Σ _ : (BG n m).edgeSet, Fin (k + 1))))
    (P' : Set (KT n m k)) (hP : ∀ p ∈ P, psiEmb n m k p ∈ P') (hP' : ∀ p' ∈ P', ∃ p ∈ P, psiEmb n m k p = p')
    (f : KT n m k → V) (hf : Function.Injective f)
    (hadj : ∀ u v, G.Adj (f u) (f v) ↔ (webOf (KG n m k) P').Adj u v) :
    Nonempty (webOf (SD (BG n m) k) P ↪g G) := by
  have E1 : webOf (SD (BG n m) k) P ↪g webOf (KG n m k) P' :=
    webOfEmb (psiEmb n m k) P P' hP (by
      intro p' hp' x y hxy ha hb
      obtain ⟨p, hpP, rfl⟩ := hP' p' hp'
      rw [webOf_adj]
      exact Or.inr ⟨hxy, p, hpP, (psiEmb n m k).map_rel_iff.1 ha, (psiEmb n m k).map_rel_iff.1 hb⟩)
  exact ⟨E1.trans ⟨⟨f, hf⟩, fun {a b} => (hadj a b)⟩⟩

theorem emb_of_spec {V : Type} (G : SimpleGraph V) (r m : ℕ) (wa wb : Bool)
    (f : KT m m (r - 1) → V) (hf : Function.Injective f)
    (hadj : ∀ u v, G.Adj (f u) (f v) ↔ R m m (r - 1) wa wb u v) :
    Nonempty (subdividedBiclique r m m ↪g G) ∨ Nonempty (biweb r m m ↪g G) ∨
      Nonempty (mixweb r m m ↪g G) := by
  have hmix : ∀ (f : KT m m (r - 1) → V), Function.Injective f →
      (∀ u v, G.Adj (f u) (f v) ↔ R m m (r - 1) true false u v) →
      Nonempty (mixweb r m m ↪g G) := by
    intro f hf hadj
    refine webSD_emb G (Set.range (fun i : Fin m => (Sum.inl (Sum.inl i) : (Fin m ⊕ Fin m) ⊕
      (Σ _ : (BG m m).edgeSet, Fin (r - 1 + 1)))))
      (Set.range (fun i : Fin m => (Sum.inl (Sum.inl i) : KT m m (r - 1)))) ?_ ?_ f hf
      (fun u v => (hadj u v).trans (webMix_adj u v).symm)
    · rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩
    · rintro _ ⟨i, rfl⟩; exact ⟨_, ⟨i, rfl⟩, rfl⟩
  cases wa <;> cases wb
  · left
    exact ⟨(psiEmb m m (r - 1)).trans ⟨⟨f, hf⟩, fun {a b} => (hadj a b).trans (R_ff a b)⟩⟩
  · right; right
    refine hmix (f ∘ swapT m (r - 1)) (hf.comp ?_) ?_
    · intro a b h
      have := congrArg (swapT m (r - 1)) h
      rwa [swapT_swapT, swapT_swapT] at this
    · intro u v
      simp only [Function.comp]
      rw [hadj, R_swap]
  · right; right
    exact hmix f hf hadj
  · right; left
    exact webSD_emb G (Set.range Sum.inl) (Set.range Sum.inl) (by rintro _ ⟨w, rfl⟩; exact ⟨w, rfl⟩)
      (by rintro _ ⟨w, rfl⟩; exact ⟨_, ⟨w, rfl⟩, rfl⟩) f hf
      (fun u v => (hadj u v).trans (webBoth_adj u v).symm)

end webs

end FatFlat.Dev.L66Pat
end

section
set_option autoImplicit false

namespace FatFlat.Dev.L66Path

variable {V : Type}

/-- a walk of length `n` from `X` to `Y` inside `U`, as a sequence -/
def Good (G : SimpleGraph V) (U X Y : Set V) (n : ℕ) (p : ℕ → V) : Prop :=
  p 0 ∈ X ∧ p n ∈ Y ∧ (∀ u ≤ n, p u ∈ U) ∧ ∀ u < n, G.Adj (p u) (p (u + 1))

structure Shortest (G : SimpleGraph V) (U X Y : Set V) (n : ℕ) (p : ℕ → V) : Prop where
  good : Good G U X Y n p
  inj : ∀ s ≤ n, ∀ t ≤ n, s < t → p s ≠ p t
  chord : ∀ s ≤ n, ∀ t ≤ n, s + 1 < t → ¬ G.Adj (p s) (p t)
  notX : ∀ u, 0 < u → u ≤ n → p u ∉ X
  notY : ∀ u < n, p u ∉ Y
  nbX : ∀ v ∈ X, ∀ u, 2 ≤ u → u ≤ n → ¬ G.Adj v (p u)
  nbY : ∀ v ∈ Y, ∀ u, u + 2 ≤ n → ¬ G.Adj v (p u)

theorem exists_shortest (G : SimpleGraph V) (U X Y : Set V) (hX : X ⊆ U) (hY : Y ⊆ U) (L : ℕ)
    (W : ∃ (n : ℕ) (p : ℕ → V), n ≤ L ∧ Good G U X Y n p) :
    ∃ (n : ℕ) (p : ℕ → V), n ≤ L ∧ Shortest G U X Y n p := by
  classical
  have hex : ∃ n, ∃ p, Good G U X Y n p := by
    obtain ⟨n, p, -, h⟩ := W
    exact ⟨n, p, h⟩
  obtain ⟨n0, p0, hn0, hg0⟩ := W
  set n := Nat.find hex with hn
  obtain ⟨p, hp⟩ := Nat.find_spec hex
  have hmin : ∀ n' q, Good G U X Y n' q → n ≤ n' := fun n' q h => Nat.find_min' hex ⟨q, h⟩
  have hnL : n ≤ L := (hmin n0 p0 hg0).trans hn0
  refine ⟨n, p, hnL, ⟨hp, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- injective
    intro s hs t ht hst heq
    obtain ⟨h0, hn', hU, hstep⟩ := hp
    set c := t - s with hc
    have hlt : n - c < n := by omega
    refine absurd (hmin (n - c) (fun w => if w ≤ s then p w else p (w + c)) ⟨?_, ?_, ?_, ?_⟩) (by omega)
    · simpa using h0
    · by_cases h : n - c ≤ s
      · have ht' : t = n := by omega
        have e : n - c = s := by omega
        show (if n - c ≤ s then p (n - c) else p (n - c + c)) ∈ Y
        rw [if_pos h, e, heq, ht']; exact hn'
      · simp only [h, if_false]
        have : n - c + c = n := by omega
        rw [this]; exact hn'
    · intro w hw
      by_cases h : w ≤ s
      · simp only [h, if_true]; exact hU w (by omega)
      · simp only [h, if_false]; exact hU _ (by omega)
    · intro w hw
      by_cases h : w + 1 ≤ s
      · have h' : w ≤ s := by omega
        simp only [h, h', if_true]; exact hstep w (by omega)
      · by_cases h' : w ≤ s
        · have : w = s := by omega
          subst this
          have h2 : ¬ (w + 1 ≤ w) := by omega
          simp only [h', h2, if_true, if_false]
          have : w + 1 + c = t + 1 := by omega
          rw [this, heq]
          exact hstep t (by omega)
        · simp only [h', h, if_false]
          have : w + 1 + c = (w + c) + 1 := by omega
          rw [this]
          exact hstep _ (by omega)
  · -- chords
    intro s hs t ht hst hadj
    obtain ⟨h0, hn', hU, hstep⟩ := hp
    set c := t - s - 1 with hc
    have hlt : n - c < n := by omega
    refine absurd (hmin (n - c) (fun w => if w ≤ s then p w else p (w + c)) ⟨?_, ?_, ?_, ?_⟩) (by omega)
    · simpa using h0
    · have h : ¬ n - c ≤ s := by omega
      simp only [h, if_false]
      have : n - c + c = n := by omega
      rw [this]; exact hn'
    · intro w hw
      by_cases h : w ≤ s
      · simp only [h, if_true]; exact hU w (by omega)
      · simp only [h, if_false]; exact hU _ (by omega)
    · intro w hw
      by_cases h : w + 1 ≤ s
      · have h' : w ≤ s := by omega
        simp only [h, h', if_true]; exact hstep w (by omega)
      · by_cases h' : w ≤ s
        · have : w = s := by omega
          subst this
          have h2 : ¬ (w + 1 ≤ w) := by omega
          simp only [h', h2, if_true, if_false]
          have : w + 1 + c = t := by omega
          rw [this]
          exact hadj
        · simp only [h', h, if_false]
          have : w + 1 + c = (w + c) + 1 := by omega
          rw [this]
          exact hstep _ (by omega)
  · -- notX
    intro u hu hun hX'
    obtain ⟨h0, hn', hU, hstep⟩ := hp
    refine absurd (hmin (n - u) (fun w => p (w + u)) ⟨?_, ?_, ?_, ?_⟩) (by omega)
    · simpa using hX'
    · have : n - u + u = n := by omega
      simp only [this]; exact hn'
    · intro w hw; exact hU _ (by omega)
    · intro w hw
      have : w + 1 + u = (w + u) + 1 := by omega
      simp only [this]
      exact hstep _ (by omega)
  · -- notY
    intro u hu hY'
    obtain ⟨h0, hn', hU, hstep⟩ := hp
    refine absurd (hmin u (fun w => p w) ⟨h0, hY', fun w hw => hU w (by omega), fun w hw => hstep w (by omega)⟩) (by omega)
  · -- nbX
    intro v hv u hu hun hadj
    obtain ⟨h0, hn', hU, hstep⟩ := hp
    refine absurd (hmin (n - u + 1) (fun w => if w = 0 then v else p (u + w - 1)) ⟨?_, ?_, ?_, ?_⟩) (by omega)
    · simpa using hv
    · have : n - u + 1 ≠ 0 := by omega
      simp only [this, if_false]
      have : u + (n - u + 1) - 1 = n := by omega
      rw [this]; exact hn'
    · intro w hw
      by_cases h : w = 0
      · simp only [h, if_true]; exact hX hv
      · simp only [h, if_false]; exact hU _ (by omega)
    · intro w hw
      by_cases h : w = 0
      · subst h
        simp only [if_true, Nat.zero_add, one_ne_zero, if_false]
        have : u + 1 - 1 = u := by omega
        rw [this]; exact hadj
      · have h1 : w + 1 ≠ 0 := by omega
        simp only [h, h1, if_false]
        have : u + (w + 1) - 1 = (u + w - 1) + 1 := by omega
        rw [this]
        exact hstep _ (by omega)
  · -- nbY
    intro v hv u hu hadj
    obtain ⟨h0, hn', hU, hstep⟩ := hp
    refine absurd (hmin (u + 1) (fun w => if w ≤ u then p w else v) ⟨?_, ?_, ?_, ?_⟩) (by omega)
    · simpa using h0
    · simpa using hv
    · intro w hw
      by_cases h : w ≤ u
      · simp only [h, if_true]; exact hU w (by omega)
      · simp only [h, if_false]; exact hY hv
    · intro w hw
      by_cases h : w + 1 ≤ u
      · have h' : w ≤ u := by omega
        simp only [h, h', if_true]; exact hstep w (by omega)
      · have : w = u := by omega
        subst this
        have h2 : ¬ (w + 1 ≤ w) := by omega
        simp only [h2, le_refl, if_true, if_false]
        exact hadj.symm

end FatFlat.Dev.L66Path
end

section
set_option autoImplicit false

namespace FatFlat.Dev.L66Walk
open FatFlat.Hereditary

variable {V : Type}

/-- a walk of length at most `k` from `x` to `y` inside `U`, as a sequence -/
def WalkIn (G : SimpleGraph V) (U : Set V) (x y : V) (k : ℕ) : Prop :=
  ∃ n ≤ k, ∃ p : ℕ → V, p 0 = x ∧ p n = y ∧ (∀ u ≤ n, p u ∈ U) ∧ ∀ u < n, G.Adj (p u) (p (u + 1))

variable {G : SimpleGraph V} {U : Set V}

theorem WalkIn.mono_k {x y : V} {k k' : ℕ} (h : WalkIn G U x y k) (hk : k ≤ k') : WalkIn G U x y k' := by
  obtain ⟨n, hn, p, h0, h1, h2, h3⟩ := h
  exact ⟨n, hn.trans hk, p, h0, h1, h2, h3⟩

theorem WalkIn.of_adj {x y : V} (hx : x ∈ U) (hy : y ∈ U) (h : G.Adj x y) : WalkIn G U x y 1 :=
  ⟨1, le_rfl, fun u => if u = 0 then x else y, by simp, by simp, by
    intro u hu
    by_cases h0 : u = 0
    · simp [h0, hx]
    · simp [h0, hy], by
    intro u hu
    have : u = 0 := by omega
    subst this
    simpa using h⟩

theorem WalkIn.trans {x y z : V} {k l : ℕ} (h1 : WalkIn G U x y k) (h2 : WalkIn G U y z l) :
    WalkIn G U x z (k + l) := by
  obtain ⟨n, hn, p, p0, pn, pU, pA⟩ := h1
  obtain ⟨n', hn', q, q0, qn, qU, qA⟩ := h2
  refine ⟨n + n', by omega, fun u => if u ≤ n then p u else q (u - n), ?_, ?_, ?_, ?_⟩
  · simp [p0]
  · by_cases h : n' = 0
    · subst h
      simp only [Nat.add_zero, le_refl, if_true]
      rw [pn]; simpa using q0.symm.trans qn
    · have : ¬ n + n' ≤ n := by omega
      simp only [this, if_false, Nat.add_sub_cancel_left]
      exact qn
  · intro u hu
    by_cases h : u ≤ n
    · simp only [h, if_true]; exact pU u h
    · simp only [h, if_false]; exact qU _ (by omega)
  · intro u hu
    by_cases h : u + 1 ≤ n
    · have h' : u ≤ n := by omega
      simp only [h, h', if_true]; exact pA u (by omega)
    · by_cases h' : u ≤ n
      · have : u = n := by omega
        subst this
        simp only [h, h', if_true, if_false, Nat.sub_self, Nat.add_sub_cancel_left]
        rw [pn, ← q0]
        exact qA 0 (by omega)
      · simp only [h, h', if_false]
        have : u + 1 - n = (u - n) + 1 := by omega
        rw [this]
        exact qA _ (by omega)

theorem WalkIn.symm {x y : V} {k : ℕ} (h : WalkIn G U x y k) : WalkIn G U y x k := by
  obtain ⟨n, hn, p, p0, pn, pU, pA⟩ := h
  refine ⟨n, hn, fun u => p (n - u), by simpa using pn, by simpa using p0, ?_, ?_⟩
  · intro u hu; exact pU _ (by omega)
  · intro u hu
    have := (pA (n - (u + 1)) (by omega)).symm
    have e : n - (u + 1) + 1 = n - u := by omega
    rw [e] at this
    exact this

theorem WalkIn.mono_U {x y : V} {k : ℕ} {U' : Set V} (h : WalkIn G U x y k) (hU : U ⊆ U') :
    WalkIn G U' x y k := by
  obtain ⟨n, hn, p, p0, pn, pU, pA⟩ := h
  exact ⟨n, hn, p, p0, pn, fun u hu => hU (pU u hu), pA⟩

/-- from the induced graph on `S` to a walk in `G` inside `S` -/
theorem walkIn_of_induce {S : Set V} {x y : S} (w : (G.induce S).Walk x y) :
    WalkIn G S x.val y.val w.length := by
  refine ⟨w.length, le_rfl, fun u => (w.getVert u).val, by simp, by simp, ?_, ?_⟩
  · intro u _; exact (w.getVert u).2
  · intro u hu
    exact w.adj_getVert_succ hu

theorem edist_mono {S S' : Set V} (h : S ⊆ S') (x y : S) :
    (G.induce S').edist ⟨x.val, h x.2⟩ ⟨y.val, h y.2⟩ ≤ (G.induce S).edist x y := by
  by_cases ht : (G.induce S).edist x y = ⊤
  · rw [ht]; exact le_top
  · obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_ne_top ht
    rw [← hw]
    exact SimpleGraph.edist_le (w.map (G.induceHomOfLE h).toHom) |>.trans (by
      rw [SimpleGraph.Walk.length_map])

theorem walkIn_radius {S : Set V} {d : ℕ} (h : RadiusLE G S d) {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    WalkIn G S x y (2 * d) := by
  obtain ⟨c, hc⟩ := h
  have key : ∀ z : S, WalkIn G S c.val z.val d := by
    intro z
    have h1 := hc z
    have ht : (G.induce S).edist c z ≠ ⊤ := ne_top_of_le_ne_top (by simp) h1
    obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_ne_top ht
    have := walkIn_of_induce w
    refine this.mono_k ?_
    have : (w.length : ℕ∞) ≤ d := hw ▸ h1
    exact_mod_cast this
  have e := ((key ⟨x, hx⟩).symm.trans (key ⟨y, hy⟩))
  exact e.mono_k (by omega)

theorem edist_leaf {S S' : Set V} (hS : S ⊆ S') {d : ℕ} {c : V} (hc : c ∈ S)
    (hrad : ∀ v : S, (G.induce S).edist ⟨c, hc⟩ v ≤ d) {a x : V} (ha : a ∈ S) (hx : x ∈ S')
    (hadj : G.Adj a x) :
    (G.induce S').edist ⟨c, hS hc⟩ ⟨x, hx⟩ ≤ ((d + 1 : ℕ) : ℕ∞) := by
  have h1 : (G.induce S').edist ⟨c, hS hc⟩ ⟨a, hS ha⟩ ≤ d :=
    (edist_mono hS ⟨c, hc⟩ ⟨a, ha⟩).trans (hrad ⟨a, ha⟩)
  have h2 : (G.induce S').edist ⟨a, hS ha⟩ ⟨x, hx⟩ = 1 :=
    SimpleGraph.edist_eq_one_iff_adj.2 hadj
  calc (G.induce S').edist ⟨c, hS hc⟩ ⟨x, hx⟩
      ≤ (G.induce S').edist ⟨c, hS hc⟩ ⟨a, hS ha⟩ + (G.induce S').edist ⟨a, hS ha⟩ ⟨x, hx⟩ :=
        SimpleGraph.edist_triangle
    _ ≤ (d : ℕ∞) + 1 := by rw [h2]; exact add_le_add_left h1 _ |>.trans_eq rfl
    _ = ((d + 1 : ℕ) : ℕ∞) := by push_cast; rfl

end FatFlat.Dev.L66Walk
end

section
set_option autoImplicit false

namespace FatFlat.Dev.L66Ext
open FatFlat.Hereditary FatFlat.Dev.L66Pat FatFlat.Dev.L66Path FatFlat.Dev.L66Walk

variable {V : Type}

/-- an induced-minor model of the coordinate graph `K(3, M, M)` with radius at most `d` -/
structure Ctx (G : SimpleGraph V) (M d : ℕ) where
  B : KT M M 2 → Set V
  disj : ∀ u w, u ≠ w → Disjoint (B u) (B w)
  adj_iff : ∀ u w, u ≠ w → ((∃ x ∈ B u, ∃ y ∈ B w, G.Adj x y) ↔ (KG M M 2).Adj u w)
  rad : ∀ w, RadiusLE G (B w) d

variable {G : SimpleGraph V} {M d : ℕ}

abbrev aL (M : ℕ) (i : Fin M) : KT M M 2 := Sum.inl (Sum.inl i)
abbrev bL (M : ℕ) (j : Fin M) : KT M M 2 := Sum.inl (Sum.inr j)
abbrev sL (M : ℕ) (i j : Fin M) (t : Fin (2 + 1)) : KT M M 2 := Sum.inr (i, j, t)

theorem Ctx.uniq (C : Ctx G M d) {v : V} {w w' : KT M M 2} (h : v ∈ C.B w) (h' : v ∈ C.B w') :
    w = w' := by
  by_contra hne
  exact Set.disjoint_left.1 (C.disj w w' hne) h h'

theorem Ctx.lab_adj (C : Ctx G M d) {v v' : V} {w w' : KT M M 2} (h : v ∈ C.B w) (h' : v' ∈ C.B w')
    (hadj : G.Adj v v') : w = w' ∨ (KG M M 2).Adj w w' := by
  by_cases hw : w = w'
  · exact Or.inl hw
  · exact Or.inr ((C.adj_iff w w' hw).1 ⟨v, h, v', h', hadj⟩)

theorem Ctx.sep (C : Ctx G M d) {v v' : V} {w w' : KT M M 2} (h : v ∈ C.B w) (h' : v' ∈ C.B w')
    (hne : w ≠ w') (hna : ¬ (KG M M 2).Adj w w') : v ≠ v' ∧ ¬ G.Adj v v' := by
  refine ⟨fun e => hne (C.uniq h (e ▸ h')), fun hadj => ?_⟩
  rcases C.lab_adj h h' hadj with e | e
  · exact hne e
  · exact hna e

/-- the union of the branch sets of the `i`-th `A`, the `ij`-th path and the `j`-th `B` -/
def Ctx.U (C : Ctx G M d) (i j : Fin M) : Set V :=
  C.B (aL M i) ∪ (⋃ t : Fin (2 + 1), C.B (sL M i j t)) ∪ C.B (bL M j)

structure PathData (C : Ctx G M d) (i j : Fin M) (n : ℕ) (p : ℕ → V) : Prop where
  four : 4 ≤ n
  le : n ≤ 6 * d + 4
  sh : Shortest G (C.U i j) (C.B (aL M i)) (C.B (bL M j)) n p
  x : p 1 ∈ C.B (sL M i j 0)
  y : p (n - 1) ∈ C.B (sL M i j 2)
  mid : ∀ u, 1 ≤ u → u ≤ n - 1 → ∃ t, p u ∈ C.B (sL M i j t)

theorem Ctx.path_exists (C : Ctx G M d) (i j : Fin M) : ∃ n p, PathData C i j n p := by
  have hsub : ∀ t : Fin (2 + 1), C.B (sL M i j t) ⊆ C.U i j := fun t v hv =>
    Or.inl (Or.inr (Set.mem_iUnion.2 ⟨t, hv⟩))
  have hAU : C.B (aL M i) ⊆ C.U i j := fun v hv => Or.inl (Or.inl hv)
  have hBU : C.B (bL M j) ⊆ C.U i j := fun v hv => Or.inr hv
  -- the four connecting edges
  have e1 : ∃ a0 ∈ C.B (aL M i), ∃ x0 ∈ C.B (sL M i j 0), G.Adj a0 x0 := by
    refine (C.adj_iff _ _ (by simp)).2 ?_
    simp [KG_inl_inr]
  have e2 : ∃ x1 ∈ C.B (sL M i j 0), ∃ z1 ∈ C.B (sL M i j 1), G.Adj x1 z1 := by
    refine (C.adj_iff _ _ (by simp)).2 ?_
    simp [KG_inr_inr]
  have e3 : ∃ z2 ∈ C.B (sL M i j 1), ∃ y2 ∈ C.B (sL M i j 2), G.Adj z2 y2 := by
    refine (C.adj_iff _ _ (by simp)).2 ?_
    simp [KG_inr_inr]
  have e4 : ∃ y3 ∈ C.B (sL M i j 2), ∃ b0 ∈ C.B (bL M j), G.Adj y3 b0 := by
    have := (C.adj_iff (bL M j) (sL M i j 2) (by simp)).2 (by simp [KG_inl_inr])
    obtain ⟨b0, hb0, y3, hy3, hadj⟩ := this
    exact ⟨y3, hy3, b0, hb0, hadj.symm⟩
  obtain ⟨a0, ha0, x0, hx0, h1⟩ := e1
  obtain ⟨x1, hx1, z1, hz1, h2⟩ := e2
  obtain ⟨z2, hz2, y2, hy2, h3⟩ := e3
  obtain ⟨y3, hy3, b0, hb0, h4⟩ := e4
  have w1 : WalkIn G (C.U i j) a0 x0 1 := WalkIn.of_adj (hAU ha0) (hsub _ hx0) h1
  have w2 : WalkIn G (C.U i j) x0 x1 (2 * d) :=
    (walkIn_radius (C.rad _) hx0 hx1).mono_U (hsub _)
  have w3 : WalkIn G (C.U i j) x1 z1 1 := WalkIn.of_adj (hsub _ hx1) (hsub _ hz1) h2
  have w4 : WalkIn G (C.U i j) z1 z2 (2 * d) :=
    (walkIn_radius (C.rad _) hz1 hz2).mono_U (hsub _)
  have w5 : WalkIn G (C.U i j) z2 y2 1 := WalkIn.of_adj (hsub _ hz2) (hsub _ hy2) h3
  have w6 : WalkIn G (C.U i j) y2 y3 (2 * d) :=
    (walkIn_radius (C.rad _) hy2 hy3).mono_U (hsub _)
  have w7 : WalkIn G (C.U i j) y3 b0 1 := WalkIn.of_adj (hsub _ hy3) (hBU hb0) h4
  have wall := ((((((w1.trans w2).trans w3).trans w4).trans w5).trans w6).trans w7).mono_k
    (show 1 + 2 * d + 1 + 2 * d + 1 + 2 * d + 1 ≤ 6 * d + 4 by omega)
  obtain ⟨n0, hn0, p0, hp00, hp0n, hp0U, hp0A⟩ := wall
  obtain ⟨n, p, hnL, hsh⟩ := exists_shortest G (C.U i j) (C.B (aL M i)) (C.B (bL M j)) hAU hBU
    (6 * d + 4) ⟨n0, p0, hn0, by rw [hp00]; exact ha0, by rw [hp0n]; exact hb0, hp0U, hp0A⟩
  obtain ⟨⟨p0X, pnY, pU, pA⟩, -⟩ := hsh.good, hsh.inj
  -- interior vertices lie in the S-branch sets
  have hmid : ∀ u, 1 ≤ u → u ≤ n - 1 → ∃ t, p u ∈ C.B (sL M i j t) := by
    intro u hu1 hu2
    have hn1 : 1 ≤ n := by omega
    have hmem := pU u (by omega)
    rcases hmem with (hA | hS) | hB
    · exact absurd hA (hsh.notX u (by omega) (by omega))
    · obtain ⟨t, ht⟩ := Set.mem_iUnion.1 hS
      exact ⟨t, ht⟩
    · exact absurd hB (hsh.notY u (by omega))
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn : n = 0 ∨ n = 1 := by omega
    rcases hn with rfl | rfl
    · exact Set.disjoint_left.1 (C.disj (aL M i) (bL M j) (by simp)) p0X pnY
    · rcases C.lab_adj p0X pnY (pA 0 (by omega)) with e | e
      · simp at e
      · simp [KG_inl_inl] at e
  obtain ⟨t1, ht1⟩ := hmid 1 le_rfl (by omega)
  obtain ⟨t2, ht2⟩ := hmid (n - 1) (by omega) le_rfl
  have hx : t1 = 0 := by
    have hadj := pA 0 (by omega)
    rcases C.lab_adj p0X ht1 hadj with e | e
    · simp at e
    · rw [KG_inl_inr] at e
      rcases e with ⟨-, e⟩ | ⟨e, -⟩
      · exact Fin.ext e
      · simp at e
  have hy : t2 = 2 := by
    have hadj := pA (n - 1) (by omega)
    have e0 : n - 1 + 1 = n := by omega
    rw [e0] at hadj
    rcases C.lab_adj ht2 pnY hadj with e | e
    · simp at e
    · rw [KG_inr_inl] at e
      rcases e with ⟨e, -⟩ | ⟨-, e⟩
      · simp at e
      · exact Fin.ext e
  subst hx hy
  refine ⟨n, p, ⟨?_, hnL, hsh, ht1, ht2, hmid⟩⟩
  by_contra hlt
  have hn : n = 2 ∨ n = 3 := by omega
  rcases hn with rfl | rfl
  · have := C.uniq ht1 ht2
    simp at this
  · have h12 := pA 1 (by omega)
    rcases C.lab_adj ht1 ht2 h12 with e | e
    · simp at e
    · rw [KG_inr_inr] at e
      exact absurd e.2.2 (by decide)

end FatFlat.Dev.L66Ext
end

section
set_option autoImplicit false

namespace FatFlat.Dev.L66Half
open FatFlat.Hereditary

variable {V : Type}

/-- an `ℓ`-fan with `ℕ`-indexed paths; `b = true` means linked, `b = false` independent -/
structure Fan (G : SimpleGraph V) (ℓ : ℕ) (b : Bool) (c : V) (X : Set V) (P : V → ℕ → V) : Prop where
  one_le : 1 ≤ ℓ
  start : ∀ x ∈ X, P x 0 = c
  finish : ∀ x ∈ X, P x ℓ = x
  inj : ∀ x ∈ X, ∀ s ≤ ℓ, ∀ t ≤ ℓ, P x s = P x t → s = t
  adj : ∀ x ∈ X, ∀ s ≤ ℓ, ∀ t ≤ ℓ, G.Adj (P x s) (P x t) ↔ (s + 1 = t ∨ t + 1 = s)
  disj : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → ∀ s t, 1 ≤ s → s ≤ ℓ → 1 ≤ t → t ≤ ℓ → P x s ≠ P y t
  link : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → ∀ s t, 1 ≤ s → s ≤ ℓ → 1 ≤ t → t ≤ ℓ →
    (G.Adj (P x s) (P y t) ↔ (b = true ∧ s = 1 ∧ t = 1))

theorem Fan.mono {G : SimpleGraph V} {ℓ : ℕ} {b : Bool} {c : V} {X Y : Set V} {P : V → ℕ → V}
    (h : Fan G ℓ b c X P) (hY : Y ⊆ X) : Fan G ℓ b c Y P where
  one_le := h.one_le
  start := fun x hx => h.start x (hY hx)
  finish := fun x hx => h.finish x (hY hx)
  inj := fun x hx => h.inj x (hY hx)
  adj := fun x hx => h.adj x (hY hx)
  disj := fun x hx y hy => h.disj x (hY hx) y (hY hy)
  link := fun x hx y hy => h.link x (hY hx) y (hY hy)

open Classical in
noncomputable def Ptr (Ap : Set V) (ℓ : ℕ) (P' : Ap → Fin (ℓ + 1) → Ap) : V → ℕ → V :=
  fun x s => if h : x ∈ Ap then (P' ⟨x, h⟩ ⟨min s ℓ, Nat.lt_succ_of_le (min_le_right _ _)⟩).val else x

lemma Ptr_eq (Ap : Set V) (ℓ : ℕ) (P' : Ap → Fin (ℓ + 1) → Ap) (x' : Ap) (s : ℕ) (hs : s ≤ ℓ) :
    Ptr Ap ℓ P' x'.val s = (P' x' ⟨s, Nat.lt_succ_of_le hs⟩).val := by
  unfold Ptr
  rw [dif_pos x'.2]
  have : min s ℓ = s := min_eq_left hs
  congr 2
  exact Fin.ext this

theorem fan_transport (G : SimpleGraph V) (Ap : Set V) (ℓ : ℕ) (c' : Ap) (X' : Finset Ap)
    (P' : Ap → Fin (ℓ + 1) → Ap) (h : IsFan (G.induce Ap) ℓ c' (X' : Set Ap) P') :
    ∃ b : Bool, Fan G ℓ b c'.val (Subtype.val '' (X' : Set Ap)) (Ptr Ap ℓ P') ∧
      ∀ x ∈ Subtype.val '' (X' : Set Ap), ∀ s ≤ ℓ, Ptr Ap ℓ P' x s ∈ Ap := by
  classical
  have hmem : ∀ x ∈ Subtype.val '' (X' : Set Ap), ∃ x' : Ap, x' ∈ X' ∧ x'.val = x := by
    rintro x ⟨x', hx', rfl⟩; exact ⟨x', hx', rfl⟩
  have key : ∀ (b : Bool), (∀ x ∈ (X' : Set Ap), ∀ y ∈ (X' : Set Ap), x ≠ y → ∀ i j : Fin (ℓ + 1), i ≠ 0 → j ≠ 0 →
      ((G.induce Ap).Adj (P' x i) (P' y j) ↔ (b = true ∧ i.val = 1 ∧ j.val = 1))) →
      Fan G ℓ b c'.val (Subtype.val '' (X' : Set Ap)) (Ptr Ap ℓ P') := by
    intro b hb
    refine ⟨h.one_le, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨x', hx', rfl⟩ := hmem x hx
      rw [Ptr_eq _ _ _ _ _ (Nat.zero_le _)]
      have := h.start x' hx'
      exact congrArg Subtype.val this
    · intro x hx
      obtain ⟨x', hx', rfl⟩ := hmem x hx
      rw [Ptr_eq _ _ _ _ _ le_rfl]
      have := h.finish x' hx'
      exact congrArg Subtype.val this
    · intro x hx s hs t ht hst
      obtain ⟨x', hx', rfl⟩ := hmem x hx
      rw [Ptr_eq _ _ _ _ _ hs, Ptr_eq _ _ _ _ _ ht] at hst
      have := h.injective x' hx' (Subtype.ext hst)
      simpa using this
    · intro x hx s hs t ht
      obtain ⟨x', hx', rfl⟩ := hmem x hx
      rw [Ptr_eq _ _ _ _ _ hs, Ptr_eq _ _ _ _ _ ht]
      exact h.induced x' hx' ⟨s, Nat.lt_succ_of_le hs⟩ ⟨t, Nat.lt_succ_of_le ht⟩
    · intro x hx y hy hxy s t hs hs' ht ht'
      obtain ⟨x', hx', rfl⟩ := hmem x hx
      obtain ⟨y', hy', rfl⟩ := hmem y hy
      rw [Ptr_eq _ _ _ _ _ hs', Ptr_eq _ _ _ _ _ ht']
      intro e
      have hne : x' ≠ y' := fun e' => hxy (by rw [e'])
      exact h.disjoint x' hx' y' hy' hne ⟨s, Nat.lt_succ_of_le hs'⟩ ⟨t, Nat.lt_succ_of_le ht'⟩
        (by intro e0; have := congrArg Fin.val e0; simp at this; omega)
        (by intro e0; have := congrArg Fin.val e0; simp at this; omega) (Subtype.ext e)
    · intro x hx y hy hxy s t hs hs' ht ht'
      obtain ⟨x', hx', rfl⟩ := hmem x hx
      obtain ⟨y', hy', rfl⟩ := hmem y hy
      rw [Ptr_eq _ _ _ _ _ hs', Ptr_eq _ _ _ _ _ ht']
      have hne : x' ≠ y' := fun e' => hxy (by rw [e'])
      have := hb x' hx' y' hy' hne ⟨s, Nat.lt_succ_of_le hs'⟩ ⟨t, Nat.lt_succ_of_le ht'⟩
        (by intro e0; have := congrArg Fin.val e0; simp at this; omega)
        (by intro e0; have := congrArg Fin.val e0; simp at this; omega)
      exact this
  have hmemAp : ∀ x ∈ Subtype.val '' (X' : Set Ap), ∀ s ≤ ℓ, Ptr Ap ℓ P' x s ∈ Ap := by
    intro x hx s hs
    obtain ⟨x', hx', rfl⟩ := hmem x hx
    rw [Ptr_eq _ _ _ _ _ hs]
    exact (P' x' _).2
  rcases h.indep_or_linked with hI | hL
  · refine ⟨false, key false ?_, hmemAp⟩
    intro x hx y hy hxy i j hi hj
    simp only [Bool.false_eq_true, false_and, iff_false]
    exact hI x hx y hy hxy i j hi hj
  · refine ⟨true, key true ?_, hmemAp⟩
    intro x hx y hy hxy i j hi hj
    simpa using hL x hx y hy hxy i j hi hj

theorem fan_step (d : ℕ) : ∃ F : ℕ → ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (Ap : Set V)
    (z : V) (hz : z ∈ Ap) (T : Finset V) (hT : ∀ x ∈ T, x ∈ Ap)
    (hd : ∀ (x : V) (hx : x ∈ T), (G.induce Ap).edist ⟨z, hz⟩ ⟨x, hT x hx⟩ ≤ ((d + 1 : ℕ) : ℕ∞))
    (s : ℕ), F s ≤ T.card → ∃ T' ⊆ T, T'.card = s ∧ ∃ (ℓ : ℕ) (b : Bool), ℓ ≤ d + 1 ∧
      ∃ (c : V) (P : V → ℕ → V), Fan G ℓ b c (T' : Set V) P ∧ c ∈ Ap ∧
        ∀ x ∈ T', ∀ s ≤ ℓ, P x s ∈ Ap := by
  obtain ⟨F, hF⟩ := FatFlat.Hereditary.lemma_6_4 (d + 1)
  refine ⟨F, ?_⟩
  intro V _ G Ap z hz T hT hd s hs
  classical
  let X : Finset Ap := T.subtype (· ∈ Ap)
  have hXcard : X.card = T.card := by
    rw [Finset.card_subtype, Finset.filter_true_of_mem hT]
  obtain ⟨X', hX'X, hX'card, ℓ, hℓ1, hℓr, hfan⟩ := hF Ap (G.induce Ap) ⟨z, hz⟩ s X
    (by rw [hXcard]; exact hs) (by
      intro x hx
      have hxT : x.val ∈ T := by simpa [X] using hx
      exact hd x.val hxT)
  obtain ⟨c', P', hP'⟩ := hfan
  obtain ⟨b, hb, hbAp⟩ := fan_transport G Ap ℓ c' X' P' hP'
  have himg : (X'.map (Function.Embedding.subtype _) : Set V) = Subtype.val '' (X' : Set Ap) := by
    ext x; simp
  refine ⟨X'.map (Function.Embedding.subtype _), ?_, by simpa using hX'card, ℓ, b, hℓr,
    c'.val, Ptr Ap ℓ P', ?_, c'.2, ?_⟩
  · intro x hx
    obtain ⟨x', hx', rfl⟩ := Finset.mem_map.1 hx
    have := hX'X hx'
    simpa [X] using this
  · rw [himg]; exact hb
  · intro x hx s hs
    apply hbAp x _ s hs
    rw [← himg]; exact hx


section iter
variable {ι κ : Type} [DecidableEq κ]

def iterN (F : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, s => s
  | n + 1, s => max (F (iterN F n s)) (iterN F n s)

theorem iterN_le (F : ℕ → ℕ) (n s : ℕ) : iterN F n s ≤ iterN F (n + 1) s := le_max_right _ _

theorem iterate_rows (Good : ι → Finset κ → Prop)
    (hmono : ∀ u J J', J' ⊆ J → Good u J → Good u J')
    (F : ℕ → ℕ)
    (hstep : ∀ u (s : ℕ) (J : Finset κ), F s ≤ J.card → ∃ J' ⊆ J, J'.card = s ∧ Good u J') :
    ∀ (n s : ℕ) (rows : Finset ι) (J0 : Finset κ), rows.card ≤ n → iterN F n s ≤ J0.card →
      ∃ J ⊆ J0, J.card = s ∧ ∀ u ∈ rows, Good u J := by
  classical
  intro n
  induction n with
  | zero =>
    intro s rows J0 hrows hJ0
    have : rows = ∅ := Finset.card_eq_zero.1 (by omega)
    subst this
    obtain ⟨J, hJ, hc⟩ := Finset.exists_subset_card_eq (show s ≤ J0.card from hJ0)
    exact ⟨J, hJ, hc, by simp⟩
  | succ n ih =>
    intro s rows J0 hrows hJ0
    by_cases hle : rows.card ≤ n
    · exact ih s rows J0 hle ((iterN_le F n s).trans hJ0)
    · have hne : rows.Nonempty := by
        rw [← Finset.card_pos]; omega
      obtain ⟨u, hu⟩ := hne
      have hcard : (rows.erase u).card ≤ n := by
        rw [Finset.card_erase_of_mem hu]; omega
      obtain ⟨J', hJ'sub, hJ'card, hgood⟩ := hstep u (iterN F n s) J0
        ((le_max_left _ _).trans hJ0)
      obtain ⟨J, hJsub, hJcard, hJgood⟩ := ih s (rows.erase u) J' hcard (by omega)
      refine ⟨J, hJsub.trans hJ'sub, hJcard, ?_⟩
      intro v hv
      by_cases hvu : v = u
      · subst hvu; exact hmono v J' J hJsub hgood
      · exact hJgood v (Finset.mem_erase.2 ⟨hvu, hv⟩)

theorem half (d : ℕ) : ∃ Nf : ℕ → ℕ → ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V)
    (ι κ : Type) [DecidableEq κ] (Ap : ι → Set V) (z : ι → V) (xs : ι → κ → V)
    (hz : ∀ u, z u ∈ Ap u) (hx : ∀ u j, xs u j ∈ Ap u) (hinj : ∀ u, Function.Injective (xs u))
    (hd : ∀ u j, (G.induce (Ap u)).edist ⟨z u, hz u⟩ ⟨xs u j, hx u j⟩ ≤ ((d + 1 : ℕ) : ℕ∞))
    (n s : ℕ) (rows : Finset ι) (J0 : Finset κ), rows.card ≤ n → Nf n s ≤ J0.card →
      ∃ J ⊆ J0, J.card = s ∧ ∀ u ∈ rows, ∃ (ℓ : ℕ) (b : Bool), ℓ ≤ d + 1 ∧
        ∃ (c : V) (P : V → ℕ → V), Fan G ℓ b c (xs u '' (J : Set κ)) P ∧ c ∈ Ap u ∧
          ∀ x ∈ xs u '' (J : Set κ), ∀ t ≤ ℓ, P x t ∈ Ap u := by
  classical
  obtain ⟨F, hF⟩ := fan_step d
  refine ⟨iterN F, ?_⟩
  intro V _ G ι κ _ Ap z xs hz hx hinj hd n s rows J0 hrows hJ0
  refine iterate_rows (fun u J => ∃ (ℓ : ℕ) (b : Bool), ℓ ≤ d + 1 ∧
        ∃ (c : V) (P : V → ℕ → V), Fan G ℓ b c (xs u '' (J : Set κ)) P ∧ c ∈ Ap u ∧
          ∀ x ∈ xs u '' (J : Set κ), ∀ t ≤ ℓ, P x t ∈ Ap u) ?_ F ?_ n s rows J0 hrows hJ0
  · rintro u J J' hJ ⟨ℓ, b, hℓ, c, P, hfan, hc, hP⟩
    have hsub : xs u '' (J' : Set κ) ⊆ xs u '' (J : Set κ) := Set.image_mono (by exact_mod_cast hJ)
    exact ⟨ℓ, b, hℓ, c, P, hfan.mono hsub, hc, fun x hx' t ht => hP x (hsub hx') t ht⟩
  · intro u s' J hJ
    have hTcard : (J.image (xs u)).card = J.card := Finset.card_image_of_injective _ (hinj u)
    obtain ⟨T', hT'sub, hT'card, ℓ, b, hℓ, c, P, hfan, hc, hP⟩ :=
      hF V G (Ap u) (z u) (hz u) (J.image (xs u))
        (by intro x hxT; obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hxT; exact hx u j)
        (by intro x hxT
            obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hxT
            exact hd u j) s' (by rw [hTcard]; exact hJ)
    refine ⟨J.filter (fun j => xs u j ∈ T'), Finset.filter_subset _ _, ?_, ?_⟩
    · have himg : (J.filter (fun j => xs u j ∈ T')).image (xs u) = T' := by
        ext x
        simp only [Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨j, ⟨-, hj⟩, rfl⟩; exact hj
        · intro hx'
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 (hT'sub hx')
          exact ⟨j, ⟨hj, hx'⟩, rfl⟩
      rw [← hT'card]
      conv_rhs => rw [← himg]
      exact (Finset.card_image_of_injective _ (hinj u)).symm
    · have himg : xs u '' ((J.filter (fun j => xs u j ∈ T') : Finset κ) : Set κ) = (T' : Set V) := by
        ext x
        simp only [Set.mem_image, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe]
        constructor
        · rintro ⟨j, ⟨-, hj⟩, rfl⟩; exact hj
        · intro hx'
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 (hT'sub hx')
          exact ⟨j, ⟨hj, hx'⟩, rfl⟩
      rw [himg]
      exact ⟨ℓ, b, hℓ, c, P, hfan, hc, fun x hx' t ht => hP x hx' t ht⟩

end iter

end FatFlat.Dev.L66Half
end

section
set_option autoImplicit false

namespace FatFlat.Dev.L66Comb

theorem pigeon {ι β : Type} [DecidableEq β] (m : ℕ) (I0 : Finset ι) (g : ι → β) (t : Finset β)
    (hg : ∀ i ∈ I0, g i ∈ t) (hc : t.card * (m - 1) < I0.card) :
    ∃ I ⊆ I0, I.card = m ∧ ∃ y ∈ t, ∀ i ∈ I, g i = y := by
  classical
  obtain ⟨y, hy, hfib⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hg hc
  have hm : m ≤ (I0.filter (fun i => g i = y)).card := by omega
  obtain ⟨I, hI, hIc⟩ := Finset.exists_subset_card_eq hm
  refine ⟨I, fun i hi => (Finset.mem_filter.1 (hI hi)).1, hIc, y, hy, fun i hi => ?_⟩
  exact (Finset.mem_filter.1 (hI hi)).2

theorem biclique_mono (q mI mJ : ℕ) :
    ∃ M₁ M₂ : ℕ, ∀ (ι κ : Type) [DecidableEq ι] [DecidableEq κ] (I0 : Finset ι) (J0 : Finset κ)
      (c : ι → κ → ℕ), (∀ i j, c i j < q) → M₁ ≤ I0.card → M₂ ≤ J0.card →
      ∃ I ⊆ I0, ∃ J ⊆ J0, I.card = mI ∧ J.card = mJ ∧ ∃ v, ∀ i ∈ I, ∀ j ∈ J, c i j = v := by
  classical
  set B := q * (mJ - 1) + 1 with hB
  refine ⟨q * B.choose mJ * (mI - 1) + 1, B, ?_⟩
  intro ι κ _ _ I0 J0 c hc hI0 hJ0
  obtain ⟨Jb, hJb, hJbc⟩ := Finset.exists_subset_card_eq hJ0
  have hrow : ∀ i, ∃ ω : ℕ × Finset κ, ω.1 < q ∧ ω.2 ∈ Jb.powersetCard mJ ∧ ∀ j ∈ ω.2, c i j = ω.1 := by
    intro i
    have hlt : (Finset.range q).card * (mJ - 1) < Jb.card := by
      rw [Finset.card_range, hJbc, hB]; omega
    obtain ⟨v, hv, hfib⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := Jb) (t := Finset.range q) (f := fun j => c i j)
      (fun j _ => Finset.mem_range.2 (hc i j)) hlt
    have hm : mJ ≤ (Jb.filter (fun j => c i j = v)).card := by omega
    obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hm
    refine ⟨(v, T), Finset.mem_range.1 hv, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨fun j hj => (Finset.mem_filter.1 (hT hj)).1, hTc⟩
    · intro j hj
      exact (Finset.mem_filter.1 (hT hj)).2
  choose ω hω1 hω2 hω3 using hrow
  have hcard : ((Finset.range q) ×ˢ (Jb.powersetCard mJ)).card * (mI - 1) < I0.card := by
    rw [Finset.card_product, Finset.card_range, Finset.card_powersetCard, hJbc]
    omega
  obtain ⟨I, hI, hIc, y, hy, hIy⟩ := pigeon mI I0 ω ((Finset.range q) ×ˢ (Jb.powersetCard mJ))
    (fun i _ => Finset.mem_product.2 ⟨Finset.mem_range.2 (hω1 i), hω2 i⟩) hcard
  refine ⟨I, hI, y.2, ?_, hIc, ?_, y.1, ?_⟩
  · intro j hj
    have := (Finset.mem_product.1 hy).2
    exact hJb ((Finset.mem_powersetCard.1 this).1 hj)
  · have := (Finset.mem_product.1 hy).2
    exact (Finset.mem_powersetCard.1 this).2
  · intro i hi j hj
    have h1 := hω3 i j (by rw [hIy i hi]; exact hj)
    rw [hIy i hi] at h1
    exact h1

end FatFlat.Dev.L66Comb
end

section
set_option autoImplicit false

namespace FatFlat.Dev.L66Frame
open FatFlat.Dev.L66Pat

variable {V : Type}

/-- explicit adjacency of two path vertices of the coordinate graph with web cliques -/
def RR (bA bB : Bool) (k : ℕ) {m : ℕ} (i j : Fin m) (t : ℕ) (i' j' : Fin m) (t' : ℕ) : Prop :=
  (i = i' ∧ j = j' ∧ (t + 1 = t' ∨ t' + 1 = t)) ∨ (bA = true ∧ i = i' ∧ j ≠ j' ∧ t = 0 ∧ t' = 0) ∨
    (bB = true ∧ i ≠ i' ∧ j = j' ∧ t = k ∧ t' = k)

theorem R_inr_inr {m k : ℕ} (wa wb : Bool) (i j : Fin m) (t : Fin (k + 1)) (i' j' : Fin m)
    (t' : Fin (k + 1)) :
    R m m k wa wb (Sum.inr (i, j, t)) (Sum.inr (i', j', t')) ↔ RR wa wb k i j t.val i' j' t'.val := by
  unfold R RR
  rw [KG_inr_inr]
  simp only [ne_eq, Sum.inr.injEq, Prod.mk.injEq]
  constructor
  · rintro (h | ⟨ha, hne, i1, j1, j2, ⟨h1, h2, h3⟩, h4, h5, h6⟩ | ⟨hb, hne, i1, i2, j1, ⟨h1, h2, h3⟩, h4, h5, h6⟩)
    · exact Or.inl h
    · subst h1 h2 h4 h5
      have t0 : t.val = 0 := by rw [h3]; rfl
      have t0' : t'.val = 0 := by rw [h6]; rfl
      exact Or.inr (Or.inl ⟨ha, rfl, fun e => hne ⟨rfl, e, Fin.ext (by omega)⟩, t0, t0'⟩)
    · subst h1 h2 h4 h5
      have t0 : t.val = k := by rw [h3]; rfl
      have t0' : t'.val = k := by rw [h6]; rfl
      exact Or.inr (Or.inr ⟨hb, fun e => hne ⟨e, rfl, Fin.ext (by omega)⟩, rfl, t0, t0'⟩)
  · rintro (h | ⟨ha, rfl, hne, h1, h2⟩ | ⟨hb, hne, rfl, h1, h2⟩)
    · exact Or.inl h
    · refine Or.inr (Or.inl ⟨ha, fun h => hne h.2.1, i, j, j', ⟨rfl, rfl, Fin.ext h1⟩, rfl, rfl, Fin.ext h2⟩)
    · refine Or.inr (Or.inr ⟨hb, fun h => hne h.1, i, i', j, ⟨rfl, rfl, Fin.ext h1⟩, rfl, rfl, Fin.ext h2⟩)

theorem RR_symm {bA bB : Bool} {k m : ℕ} (i j : Fin m) (t : ℕ) (i' j' : Fin m) (t' : ℕ) :
    RR bA bB k i j t i' j' t' ↔ RR bA bB k i' j' t' i j t := by
  unfold RR
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩)
    · exact Or.inl ⟨h1.symm, h2.symm, h3.symm⟩
    · exact Or.inr (Or.inl ⟨h1, h2.symm, h3.symm, h5, h4⟩)
    · exact Or.inr (Or.inr ⟨h1, h2.symm, h3.symm, h5, h4⟩)
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩)
    · exact Or.inl ⟨h1.symm, h2.symm, h3.symm⟩
    · exact Or.inr (Or.inl ⟨h1, h2.symm, h3.symm, h5, h4⟩)
    · exact Or.inr (Or.inr ⟨h1, h2.symm, h3.symm, h5, h4⟩)

/-- the assembled data -/
structure Frame (G : SimpleGraph V) (m ℓA ℓB n : ℕ) (bA bB : Bool) (cA cB : Fin m → V)
    (PA PB pp : Fin m → Fin m → ℕ → V) : Prop where
  hA : 1 ≤ ℓA
  hB : 1 ≤ ℓB
  hn : 4 ≤ n
  a0 : ∀ i j, PA i j 0 = cA i
  a1 : ∀ i j s, s ≤ ℓA → ∀ t, t ≤ ℓA → PA i j s = PA i j t → s = t
  a2 : ∀ i j s t, s ≤ ℓA → t ≤ ℓA → (G.Adj (PA i j s) (PA i j t) ↔ (s + 1 = t ∨ t + 1 = s))
  a3 : ∀ i j j', j ≠ j' → ∀ s t, 1 ≤ s → s ≤ ℓA → 1 ≤ t → t ≤ ℓA → PA i j s ≠ PA i j' t
  a4 : ∀ i j j', j ≠ j' → ∀ s t, 1 ≤ s → s ≤ ℓA → 1 ≤ t → t ≤ ℓA →
    (G.Adj (PA i j s) (PA i j' t) ↔ (bA = true ∧ s = 1 ∧ t = 1))
  b0 : ∀ j i, PB j i 0 = cB j
  b1 : ∀ j i s, s ≤ ℓB → ∀ t, t ≤ ℓB → PB j i s = PB j i t → s = t
  b2 : ∀ j i s t, s ≤ ℓB → t ≤ ℓB → (G.Adj (PB j i s) (PB j i t) ↔ (s + 1 = t ∨ t + 1 = s))
  b3 : ∀ j i i', i ≠ i' → ∀ s t, 1 ≤ s → s ≤ ℓB → 1 ≤ t → t ≤ ℓB → PB j i s ≠ PB j i' t
  b4 : ∀ j i i', i ≠ i' → ∀ s t, 1 ≤ s → s ≤ ℓB → 1 ≤ t → t ≤ ℓB →
    (G.Adj (PB j i s) (PB j i' t) ↔ (bB = true ∧ s = 1 ∧ t = 1))
  aa : ∀ i i', i ≠ i' → ∀ j j' s t, s ≤ ℓA → t ≤ ℓA →
    PA i j s ≠ PA i' j' t ∧ ¬ G.Adj (PA i j s) (PA i' j' t)
  bb : ∀ j j', j ≠ j' → ∀ i i' s t, s ≤ ℓB → t ≤ ℓB →
    PB j i s ≠ PB j' i' t ∧ ¬ G.Adj (PB j i s) (PB j' i' t)
  ab : ∀ i j j' i' s t, s ≤ ℓA → t ≤ ℓB →
    PA i j s ≠ PB j' i' t ∧ ¬ G.Adj (PA i j s) (PB j' i' t)
  mm : ∀ i j i' j', (i ≠ i' ∨ j ≠ j') → ∀ u u', 1 ≤ u → u ≤ n - 1 → 1 ≤ u' → u' ≤ n - 1 →
    pp i j u ≠ pp i' j' u' ∧ ¬ G.Adj (pp i j u) (pp i' j' u')
  ms1 : ∀ i j u u', 1 ≤ u → u ≤ n - 1 → 1 ≤ u' → u' ≤ n - 1 → pp i j u = pp i j u' → u = u'
  ms2 : ∀ i j u u', 1 ≤ u → u ≤ n - 1 → 1 ≤ u' → u' ≤ n - 1 →
    (G.Adj (pp i j u) (pp i j u') ↔ (u + 1 = u' ∨ u' + 1 = u))
  l1 : ∀ i j, PA i j ℓA = pp i j 1
  l2 : ∀ i j, PB j i ℓB = pp i j (n - 1)
  am1 : ∀ i j j' s u, s ≤ ℓA → 2 ≤ u → u ≤ n - 2 →
    PA i j s ≠ pp i j' u ∧ (G.Adj (PA i j s) (pp i j' u) ↔ (j = j' ∧ s = ℓA ∧ u = 2))
  am2 : ∀ i i', i ≠ i' → ∀ j j' s u, s ≤ ℓA → 2 ≤ u → u ≤ n - 2 →
    PA i j s ≠ pp i' j' u ∧ ¬ G.Adj (PA i j s) (pp i' j' u)
  bm1 : ∀ j i i' s u, s ≤ ℓB → 2 ≤ u → u ≤ n - 2 →
    PB j i s ≠ pp i' j u ∧ (G.Adj (PB j i s) (pp i' j u) ↔ (i = i' ∧ s = ℓB ∧ u = n - 2))
  bm2 : ∀ j j', j ≠ j' → ∀ i i' s u, s ≤ ℓB → 2 ≤ u → u ≤ n - 2 →
    PB j i s ≠ pp i' j' u ∧ ¬ G.Adj (PB j i s) (pp i' j' u)

section frame
variable {G : SimpleGraph V} {m ℓA ℓB n : ℕ} {bA bB : Bool} {cA cB : Fin m → V}
  {PA PB pp : Fin m → Fin m → ℕ → V}

/-- the `t`-th inner vertex of the path from `cA i` to `cB j` -/
def Qf (ℓA ℓB n : ℕ) (PA PB pp : Fin m → Fin m → ℕ → V) (i j : Fin m) (t : ℕ) : V :=
  if t < ℓA then PA i j (t + 1)
  else if t < ℓA + (n - 3) then pp i j (t - ℓA + 2)
  else PB j i (ℓA + (n - 3) + ℓB - t)

theorem Qf_A {i j : Fin m} {t : ℕ} (h : t < ℓA) : Qf ℓA ℓB n PA PB pp i j t = PA i j (t + 1) := by
  simp [Qf, h]

theorem Qf_M {i j : Fin m} {t : ℕ} (h1 : ℓA ≤ t) (h2 : t < ℓA + (n - 3)) :
    Qf ℓA ℓB n PA PB pp i j t = pp i j (t - ℓA + 2) := by
  have : ¬ t < ℓA := by omega
  simp [Qf, this, h2]

theorem Qf_B {i j : Fin m} {t : ℕ} (h1 : ℓA + (n - 3) ≤ t) :
    Qf ℓA ℓB n PA PB pp i j t = PB j i (ℓA + (n - 3) + ℓB - t) := by
  have : ¬ t < ℓA + (n - 3) := by omega
  have h' : ¬ t < ℓA := by omega
  simp [Qf, this, h']

theorem pair_AA (hF : Frame G m ℓA ℓB n bA bB cA cB PA PB pp) {i j i' j' : Fin m} {t t' : ℕ}
    (ht : t < ℓA) (ht' : t' < ℓA) :
    (Qf ℓA ℓB n PA PB pp i j t = Qf ℓA ℓB n PA PB pp i' j' t' ↔ i = i' ∧ j = j' ∧ t = t') ∧
    (G.Adj (Qf ℓA ℓB n PA PB pp i j t) (Qf ℓA ℓB n PA PB pp i' j' t') ↔
      RR bA bB (ℓA + (n - 3) + ℓB - 1) i j t i' j' t') := by
  have hB := hF.hB
  have hn := hF.hn
  rw [Qf_A ht, Qf_A ht']
  by_cases hi : i = i'
  · subst hi
    by_cases hj : j = j'
    · subst hj
      refine ⟨⟨fun h => ⟨rfl, rfl, by have := hF.a1 i j _ (by omega) _ (by omega) h; omega⟩,
        fun h => by rw [h.2.2]⟩, ?_⟩
      rw [hF.a2 i j _ _ (by omega) (by omega)]
      unfold RR
      constructor
      · rintro (h | h)
        · exact Or.inl ⟨rfl, rfl, Or.inl (by omega)⟩
        · exact Or.inl ⟨rfl, rfl, Or.inr (by omega)⟩
      · rintro (⟨-, -, h | h⟩ | ⟨-, -, h, -⟩ | ⟨-, h, -⟩)
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
        · exact absurd rfl h
        · exact absurd rfl h
    · refine ⟨⟨fun h => absurd h (hF.a3 i j j' hj _ _ (by omega) (by omega) (by omega) (by omega)),
        fun h => absurd h.2.1 hj⟩, ?_⟩
      rw [hF.a4 i j j' hj _ _ (by omega) (by omega) (by omega) (by omega)]
      unfold RR
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact Or.inr (Or.inl ⟨h1, rfl, hj, by omega, by omega⟩)
      · rintro (⟨-, h, -⟩ | ⟨h1, -, -, h2, h3⟩ | ⟨-, h, -⟩)
        · exact absurd h hj
        · exact ⟨h1, by omega, by omega⟩
        · exact absurd rfl h
  · have := hF.aa i i' hi j j' (t + 1) (t' + 1) (by omega) (by omega)
    refine ⟨⟨fun h => absurd h this.1, fun h => absurd h.1 hi⟩, ⟨fun h => absurd h this.2, ?_⟩⟩
    unfold RR
    rintro (⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, -, h, -⟩)
    · exact absurd h hi
    · exact absurd h hi
    · omega


theorem pair_AM (hF : Frame G m ℓA ℓB n bA bB cA cB PA PB pp) {i j i' j' : Fin m} {t t' : ℕ}
    (ht : t < ℓA) (ht1 : ℓA ≤ t') (ht2 : t' < ℓA + (n - 3)) :
    (Qf ℓA ℓB n PA PB pp i j t = Qf ℓA ℓB n PA PB pp i' j' t' ↔ i = i' ∧ j = j' ∧ t = t') ∧
    (G.Adj (Qf ℓA ℓB n PA PB pp i j t) (Qf ℓA ℓB n PA PB pp i' j' t') ↔
      RR bA bB (ℓA + (n - 3) + ℓB - 1) i j t i' j' t') := by
  have hA := hF.hA
  have hB := hF.hB
  have hn := hF.hn
  rw [Qf_A ht, Qf_M ht1 ht2]
  by_cases hi : i = i'
  · subst hi
    have h := hF.am1 i j j' (t + 1) (t' - ℓA + 2) (by omega) (by omega) (by omega)
    refine ⟨⟨fun e => absurd e h.1, fun e => by omega⟩, ?_⟩
    rw [h.2]
    unfold RR
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact Or.inl ⟨rfl, h1, Or.inl (by omega)⟩
    · rintro (⟨-, h1, h2 | h2⟩ | ⟨-, -, -, -, h⟩ | ⟨-, h, -⟩)
      · exact ⟨h1, by omega, by omega⟩
      · omega
      · omega
      · exact absurd rfl h
  · have h := hF.am2 i i' hi j j' (t + 1) (t' - ℓA + 2) (by omega) (by omega) (by omega)
    refine ⟨⟨fun e => absurd e h.1, fun e => absurd e.1 hi⟩, ⟨fun e => absurd e h.2, ?_⟩⟩
    unfold RR
    rintro (⟨e, -⟩ | ⟨-, e, -⟩ | ⟨-, -, -, h3, -⟩)
    · exact absurd e hi
    · exact absurd e hi
    · omega

theorem pair_AB (hF : Frame G m ℓA ℓB n bA bB cA cB PA PB pp) {i j i' j' : Fin m} {t t' : ℕ}
    (ht : t < ℓA) (ht1 : ℓA + (n - 3) ≤ t') (ht2 : t' < ℓA + (n - 3) + ℓB) :
    (Qf ℓA ℓB n PA PB pp i j t = Qf ℓA ℓB n PA PB pp i' j' t' ↔ i = i' ∧ j = j' ∧ t = t') ∧
    (G.Adj (Qf ℓA ℓB n PA PB pp i j t) (Qf ℓA ℓB n PA PB pp i' j' t') ↔
      RR bA bB (ℓA + (n - 3) + ℓB - 1) i j t i' j' t') := by
  have hA := hF.hA
  have hB := hF.hB
  have hn := hF.hn
  rw [Qf_A ht, Qf_B ht1]
  have h := hF.ab i j j' i' (t + 1) (ℓA + (n - 3) + ℓB - t') (by omega) (by omega)
  refine ⟨⟨fun e => absurd e h.1, fun e => by omega⟩, ⟨fun e => absurd e h.2, ?_⟩⟩
  unfold RR
  rintro (⟨-, -, h | h⟩ | ⟨-, -, -, -, h⟩ | ⟨-, -, -, h, -⟩) <;> omega

theorem pair_MM (hF : Frame G m ℓA ℓB n bA bB cA cB PA PB pp) {i j i' j' : Fin m} {t t' : ℕ}
    (ht1 : ℓA ≤ t) (ht2 : t < ℓA + (n - 3)) (ht1' : ℓA ≤ t') (ht2' : t' < ℓA + (n - 3)) :
    (Qf ℓA ℓB n PA PB pp i j t = Qf ℓA ℓB n PA PB pp i' j' t' ↔ i = i' ∧ j = j' ∧ t = t') ∧
    (G.Adj (Qf ℓA ℓB n PA PB pp i j t) (Qf ℓA ℓB n PA PB pp i' j' t') ↔
      RR bA bB (ℓA + (n - 3) + ℓB - 1) i j t i' j' t') := by
  have hA := hF.hA
  have hB := hF.hB
  have hn := hF.hn
  rw [Qf_M ht1 ht2, Qf_M ht1' ht2']
  by_cases hij : i = i' ∧ j = j'
  · obtain ⟨rfl, rfl⟩ := hij
    refine ⟨⟨fun e => ⟨rfl, rfl, by have := hF.ms1 i j _ _ (by omega) (by omega) (by omega) (by omega) e; omega⟩,
      fun e => by rw [e.2.2]⟩, ?_⟩
    rw [hF.ms2 i j _ _ (by omega) (by omega) (by omega) (by omega)]
    unfold RR
    constructor
    · rintro (h | h)
      · exact Or.inl ⟨rfl, rfl, Or.inl (by omega)⟩
      · exact Or.inl ⟨rfl, rfl, Or.inr (by omega)⟩
    · rintro (⟨-, -, h | h⟩ | ⟨-, -, h, -⟩ | ⟨-, h, -⟩)
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
      · exact absurd rfl h
      · exact absurd rfl h
  · have hne : i ≠ i' ∨ j ≠ j' := by
      by_contra hc
      push_neg at hc
      exact hij hc
    have h := hF.mm i j i' j' hne (t - ℓA + 2) (t' - ℓA + 2) (by omega) (by omega) (by omega) (by omega)
    refine ⟨⟨fun e => absurd e h.1, fun e => (hij ⟨e.1, e.2.1⟩).elim⟩, ⟨fun e => absurd e h.2, ?_⟩⟩
    unfold RR
    rintro (⟨e1, e2, -⟩ | ⟨-, -, -, h1, -⟩ | ⟨-, -, -, h1, -⟩)
    · exact (hij ⟨e1, e2⟩).elim
    · omega
    · omega

theorem pair_MB (hF : Frame G m ℓA ℓB n bA bB cA cB PA PB pp) {i j i' j' : Fin m} {t t' : ℕ}
    (ht1 : ℓA ≤ t) (ht2 : t < ℓA + (n - 3)) (ht1' : ℓA + (n - 3) ≤ t')
    (ht2' : t' < ℓA + (n - 3) + ℓB) :
    (Qf ℓA ℓB n PA PB pp i j t = Qf ℓA ℓB n PA PB pp i' j' t' ↔ i = i' ∧ j = j' ∧ t = t') ∧
    (G.Adj (Qf ℓA ℓB n PA PB pp i j t) (Qf ℓA ℓB n PA PB pp i' j' t') ↔
      RR bA bB (ℓA + (n - 3) + ℓB - 1) i j t i' j' t') := by
  have hA := hF.hA
  have hB := hF.hB
  have hn := hF.hn
  rw [Qf_M ht1 ht2, Qf_B ht1']
  by_cases hjj : j' = j
  · subst hjj
    have h := hF.bm1 j' i' i (ℓA + (n - 3) + ℓB - t') (t - ℓA + 2) (by omega) (by omega) (by omega)
    refine ⟨⟨fun e => absurd e.symm h.1, fun e => by omega⟩, ?_⟩
    rw [SimpleGraph.adj_comm, h.2]
    unfold RR
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact Or.inl ⟨h1.symm, rfl, Or.inl (by omega)⟩
    · rintro (⟨h1, -, h2 | h2⟩ | ⟨-, -, -, h2, -⟩ | ⟨-, -, -, h2, -⟩)
      · exact ⟨h1.symm, by omega, by omega⟩
      · omega
      · omega
      · omega
  · have h := hF.bm2 j' j hjj i' i (ℓA + (n - 3) + ℓB - t') (t - ℓA + 2) (by omega) (by omega) (by omega)
    refine ⟨⟨fun e => absurd e.symm h.1, fun e => (hjj e.2.1.symm).elim⟩, ⟨fun e => absurd e.symm h.2, ?_⟩⟩
    unfold RR
    rintro (⟨-, e, -⟩ | ⟨-, -, -, h1, -⟩ | ⟨-, -, e, -⟩)
    · exact (hjj e.symm).elim
    · omega
    · exact (hjj e.symm).elim

theorem pair_BB (hF : Frame G m ℓA ℓB n bA bB cA cB PA PB pp) {i j i' j' : Fin m} {t t' : ℕ}
    (ht1 : ℓA + (n - 3) ≤ t) (ht2 : t < ℓA + (n - 3) + ℓB) (ht1' : ℓA + (n - 3) ≤ t')
    (ht2' : t' < ℓA + (n - 3) + ℓB) :
    (Qf ℓA ℓB n PA PB pp i j t = Qf ℓA ℓB n PA PB pp i' j' t' ↔ i = i' ∧ j = j' ∧ t = t') ∧
    (G.Adj (Qf ℓA ℓB n PA PB pp i j t) (Qf ℓA ℓB n PA PB pp i' j' t') ↔
      RR bA bB (ℓA + (n - 3) + ℓB - 1) i j t i' j' t') := by
  have hA := hF.hA
  have hB := hF.hB
  have hn := hF.hn
  rw [Qf_B ht1, Qf_B ht1']
  by_cases hj : j = j'
  · subst hj
    by_cases hi : i = i'
    · subst hi
      refine ⟨⟨fun e => ⟨rfl, rfl, by
          have := hF.b1 j i _ (by omega) _ (by omega) e; omega⟩, fun e => by rw [e.2.2]⟩, ?_⟩
      rw [hF.b2 j i _ _ (by omega) (by omega)]
      unfold RR
      constructor
      · rintro (h | h)
        · exact Or.inl ⟨rfl, rfl, Or.inr (by omega)⟩
        · exact Or.inl ⟨rfl, rfl, Or.inl (by omega)⟩
      · rintro (⟨-, -, h | h⟩ | ⟨-, -, h, -⟩ | ⟨-, h, -⟩)
        · exact Or.inr (by omega)
        · exact Or.inl (by omega)
        · exact absurd rfl h
        · exact absurd rfl h
    · refine ⟨⟨fun e => absurd e (hF.b3 j i i' hi _ _ (by omega) (by omega) (by omega) (by omega)),
        fun e => absurd e.1 hi⟩, ?_⟩
      rw [hF.b4 j i i' hi _ _ (by omega) (by omega) (by omega) (by omega)]
      unfold RR
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact Or.inr (Or.inr ⟨h1, hi, rfl, by omega, by omega⟩)
      · rintro (⟨h, -⟩ | ⟨-, h, -⟩ | ⟨h1, -, -, h2, h3⟩)
        · exact absurd h hi
        · exact absurd h hi
        · exact ⟨h1, by omega, by omega⟩
  · have h := hF.bb j j' hj i i' (ℓA + (n - 3) + ℓB - t) (ℓA + (n - 3) + ℓB - t') (by omega) (by omega)
    refine ⟨⟨fun e => absurd e h.1, fun e => (hj e.2.1).elim⟩, ⟨fun e => absurd e h.2, ?_⟩⟩
    unfold RR
    rintro (⟨-, e, -⟩ | ⟨-, -, -, h1, -⟩ | ⟨-, -, e, -⟩)
    · exact (hj e).elim
    · omega
    · exact (hj e).elim

theorem pair_QQ (hF : Frame G m ℓA ℓB n bA bB cA cB PA PB pp) {i j i' j' : Fin m} {t t' : ℕ}
    (ht : t < ℓA + (n - 3) + ℓB) (ht' : t' < ℓA + (n - 3) + ℓB) :
    (Qf ℓA ℓB n PA PB pp i j t = Qf ℓA ℓB n PA PB pp i' j' t' ↔ i = i' ∧ j = j' ∧ t = t') ∧
    (G.Adj (Qf ℓA ℓB n PA PB pp i j t) (Qf ℓA ℓB n PA PB pp i' j' t') ↔
      RR bA bB (ℓA + (n - 3) + ℓB - 1) i j t i' j' t') := by
  have flip : ∀ {i j i' j' : Fin m} {t t' : ℕ},
      ((Qf ℓA ℓB n PA PB pp i' j' t' = Qf ℓA ℓB n PA PB pp i j t ↔ i' = i ∧ j' = j ∧ t' = t) ∧
      (G.Adj (Qf ℓA ℓB n PA PB pp i' j' t') (Qf ℓA ℓB n PA PB pp i j t) ↔
        RR bA bB (ℓA + (n - 3) + ℓB - 1) i' j' t' i j t)) →
      ((Qf ℓA ℓB n PA PB pp i j t = Qf ℓA ℓB n PA PB pp i' j' t' ↔ i = i' ∧ j = j' ∧ t = t') ∧
      (G.Adj (Qf ℓA ℓB n PA PB pp i j t) (Qf ℓA ℓB n PA PB pp i' j' t') ↔
        RR bA bB (ℓA + (n - 3) + ℓB - 1) i j t i' j' t')) := by
    intro i j i' j' t t' h
    refine ⟨⟨fun e => ?_, fun e => ?_⟩, ?_⟩
    · have := h.1.1 e.symm; exact ⟨this.1.symm, this.2.1.symm, this.2.2.symm⟩
    · exact (h.1.2 ⟨e.1.symm, e.2.1.symm, e.2.2.symm⟩).symm
    · rw [SimpleGraph.adj_comm, h.2, RR_symm]
  rcases lt_or_ge t ℓA with h1 | h1 <;> rcases lt_or_ge t' ℓA with h2 | h2
  · exact pair_AA hF h1 h2
  · rcases lt_or_ge t' (ℓA + (n - 3)) with h3 | h3
    · exact pair_AM hF h1 h2 h3
    · exact pair_AB hF h1 h3 ht'
  · rcases lt_or_ge t (ℓA + (n - 3)) with h3 | h3
    · exact flip (pair_AM hF h2 h1 h3)
    · exact flip (pair_AB hF h2 h3 ht)
  · rcases lt_or_ge t (ℓA + (n - 3)) with h3 | h3 <;> rcases lt_or_ge t' (ℓA + (n - 3)) with h4 | h4
    · exact pair_MM hF h1 h3 h2 h4
    · exact pair_MB hF h1 h3 h4 ht'
    · exact flip (pair_MB hF h2 h4 h3 ht)
    · exact pair_BB hF h3 ht h4 ht'


theorem cen_AQ (hF : Frame G m ℓA ℓB n bA bB cA cB PA PB pp) {i i' j : Fin m} {t : ℕ}
    (ht : t < ℓA + (n - 3) + ℓB) :
    cA i ≠ Qf ℓA ℓB n PA PB pp i' j t ∧
      (G.Adj (cA i) (Qf ℓA ℓB n PA PB pp i' j t) ↔ i = i' ∧ t = 0) := by
  have hA := hF.hA
  have hB := hF.hB
  have hn := hF.hn
  have e : cA i = PA i j 0 := (hF.a0 i j).symm
  rw [e]
  rcases lt_or_ge t ℓA with h1 | h1
  · rw [Qf_A h1]
    by_cases hi : i = i'
    · subst hi
      refine ⟨fun h => by have := hF.a1 i j 0 (by omega) (t + 1) (by omega) h; omega, ?_⟩
      rw [hF.a2 i j 0 (t + 1) (by omega) (by omega)]
      constructor
      · rintro (h | h)
        · exact ⟨rfl, by omega⟩
        · omega
      · rintro ⟨-, h⟩; left; omega
    · have := hF.aa i i' hi j j 0 (t + 1) (by omega) (by omega)
      exact ⟨this.1, ⟨fun h => absurd h this.2, fun h => absurd h.1 hi⟩⟩
  · rcases lt_or_ge t (ℓA + (n - 3)) with h2 | h2
    · rw [Qf_M h1 h2]
      by_cases hi : i = i'
      · subst hi
        have := hF.am1 i j j 0 (t - ℓA + 2) (by omega) (by omega) (by omega)
        refine ⟨this.1, ⟨fun h => ?_, fun h => by omega⟩⟩
        have := this.2.1 h
        omega
      · have := hF.am2 i i' hi j j 0 (t - ℓA + 2) (by omega) (by omega) (by omega)
        exact ⟨this.1, ⟨fun h => absurd h this.2, fun h => absurd h.1 hi⟩⟩
    · rw [Qf_B h2]
      have := hF.ab i j j i' 0 (ℓA + (n - 3) + ℓB - t) (by omega) (by omega)
      exact ⟨this.1, ⟨fun h => absurd h this.2, fun h => by omega⟩⟩

theorem cen_BQ (hF : Frame G m ℓA ℓB n bA bB cA cB PA PB pp) {j i' j' : Fin m} {t : ℕ}
    (ht : t < ℓA + (n - 3) + ℓB) :
    cB j ≠ Qf ℓA ℓB n PA PB pp i' j' t ∧
      (G.Adj (cB j) (Qf ℓA ℓB n PA PB pp i' j' t) ↔ j = j' ∧ t = ℓA + (n - 3) + ℓB - 1) := by
  have hA := hF.hA
  have hB := hF.hB
  have hn := hF.hn
  have e : cB j = PB j i' 0 := (hF.b0 j i').symm
  rw [e]
  rcases lt_or_ge t ℓA with h1 | h1
  · rw [Qf_A h1]
    have := hF.ab i' j' j i' (t + 1) 0 (by omega) (by omega)
    exact ⟨fun h => this.1 h.symm, ⟨fun h => absurd h.symm this.2, fun h => by omega⟩⟩
  · rcases lt_or_ge t (ℓA + (n - 3)) with h2 | h2
    · rw [Qf_M h1 h2]
      by_cases hj : j = j'
      · subst hj
        have := hF.bm1 j i' i' 0 (t - ℓA + 2) (by omega) (by omega) (by omega)
        refine ⟨this.1, ⟨fun h => ?_, fun h => by omega⟩⟩
        have := this.2.1 h
        omega
      · have := hF.bm2 j j' hj i' i' 0 (t - ℓA + 2) (by omega) (by omega) (by omega)
        exact ⟨this.1, ⟨fun h => absurd h this.2, fun h => absurd h.1 hj⟩⟩
    · rw [Qf_B h2]
      by_cases hj : j = j'
      · subst hj
        refine ⟨fun h => by have := hF.b1 j i' 0 (by omega) _ (by omega) h; omega, ?_⟩
        rw [hF.b2 j i' 0 _ (by omega) (by omega)]
        constructor
        · rintro (h | h)
          · exact ⟨rfl, by omega⟩
          · omega
        · rintro ⟨-, h⟩; left; omega
      · have := hF.bb j j' hj i' i' 0 (ℓA + (n - 3) + ℓB - t) (by omega) (by omega)
        exact ⟨this.1, ⟨fun h => absurd h this.2, fun h => absurd h.1 hj⟩⟩

theorem cen_AA (hF : Frame G m ℓA ℓB n bA bB cA cB PA PB pp) (i i' : Fin m) :
    (cA i = cA i' ↔ i = i') ∧ ¬ G.Adj (cA i) (cA i') := by
  by_cases hi : i = i'
  · subst hi; exact ⟨⟨fun _ => rfl, fun _ => rfl⟩, G.loopless.irrefl _⟩
  · have := hF.aa i i' hi i i 0 0 (by have := hF.hA; omega) (by have := hF.hA; omega)
    rw [hF.a0, hF.a0] at this
    exact ⟨⟨fun h => absurd h this.1, fun h => absurd h hi⟩, this.2⟩

theorem cen_BB (hF : Frame G m ℓA ℓB n bA bB cA cB PA PB pp) (j j' : Fin m) :
    (cB j = cB j' ↔ j = j') ∧ ¬ G.Adj (cB j) (cB j') := by
  by_cases hj : j = j'
  · subst hj; exact ⟨⟨fun _ => rfl, fun _ => rfl⟩, G.loopless.irrefl _⟩
  · have := hF.bb j j' hj j j 0 0 (by have := hF.hB; omega) (by have := hF.hB; omega)
    rw [hF.b0, hF.b0] at this
    exact ⟨⟨fun h => absurd h this.1, fun h => absurd h hj⟩, this.2⟩

theorem cen_AB (hF : Frame G m ℓA ℓB n bA bB cA cB PA PB pp) (i j : Fin m) :
    cA i ≠ cB j ∧ ¬ G.Adj (cA i) (cB j) := by
  have := hF.ab i j j i 0 0 (by have := hF.hA; omega) (by have := hF.hB; omega)
  rw [hF.a0, hF.b0] at this
  exact this

/-- the assembled vertex map -/
def fmap (ℓA ℓB n : ℕ) (cA cB : Fin m → V) (PA PB pp : Fin m → Fin m → ℕ → V) {k : ℕ} :
    KT m m k → V
  | Sum.inl (Sum.inl i) => cA i
  | Sum.inl (Sum.inr j) => cB j
  | Sum.inr (i, j, t) => Qf ℓA ℓB n PA PB pp i j t.val

theorem R_inlA_inr {k : ℕ} (wa wb : Bool) (i i' : Fin m) (j' : Fin m) (t' : Fin (k + 1)) :
    R m m k wa wb (Sum.inl (Sum.inl i)) (Sum.inr (i', j', t')) ↔ i = i' ∧ t'.val = 0 := by
  unfold R; simp [KG_inl_inr]

theorem R_inlB_inr {k : ℕ} (wa wb : Bool) (j i' j' : Fin m) (t' : Fin (k + 1)) :
    R m m k wa wb (Sum.inl (Sum.inr j)) (Sum.inr (i', j', t')) ↔ j = j' ∧ t'.val = k := by
  unfold R; simp [KG_inl_inr]

theorem R_inr_inlA {k : ℕ} (wa wb : Bool) (i i' : Fin m) (j' : Fin m) (t' : Fin (k + 1)) :
    R m m k wa wb (Sum.inr (i', j', t')) (Sum.inl (Sum.inl i)) ↔ i = i' ∧ t'.val = 0 := by
  unfold R; simp [KG_inr_inl]

theorem R_inr_inlB {k : ℕ} (wa wb : Bool) (j i' j' : Fin m) (t' : Fin (k + 1)) :
    R m m k wa wb (Sum.inr (i', j', t')) (Sum.inl (Sum.inr j)) ↔ j = j' ∧ t'.val = k := by
  unfold R; simp [KG_inr_inl]

theorem R_inl_inl {k : ℕ} (wa wb : Bool) (u v : Fin m ⊕ Fin m) :
    ¬ R m m k wa wb (Sum.inl u) (Sum.inl v) := by
  unfold R; simp [KG_inl_inl]

theorem frame_embed (hF : Frame G m ℓA ℓB n bA bB cA cB PA PB pp) :
    ∃ f : KT m m (ℓA + (n - 3) + ℓB - 1) → V, Function.Injective f ∧
      ∀ u v, G.Adj (f u) (f v) ↔ R m m (ℓA + (n - 3) + ℓB - 1) bA bB u v := by
  have hA := hF.hA
  have hB := hF.hB
  have hn := hF.hn
  have hlt : ∀ t : Fin (ℓA + (n - 3) + ℓB - 1 + 1), t.val < ℓA + (n - 3) + ℓB := fun t => by
    have := t.2; omega
  refine ⟨fmap ℓA ℓB n cA cB PA PB pp, ?_, ?_⟩
  · rintro (u | ⟨i, j, t⟩) (v | ⟨i', j', t'⟩) h
    · rcases u with i | j <;> rcases v with i' | j'
      · exact congrArg (fun x => (Sum.inl (Sum.inl x) : KT m m _)) ((cen_AA hF i i').1.1 h)
      · exact absurd h (cen_AB hF i j').1
      · exact absurd h.symm (cen_AB hF i' j).1
      · exact congrArg (fun x => (Sum.inl (Sum.inr x) : KT m m _)) ((cen_BB hF j j').1.1 h)
    · rcases u with i | j
      · exact absurd h (cen_AQ hF (hlt t')).1
      · exact absurd h (cen_BQ hF (hlt t')).1
    · rcases v with i' | j'
      · exact absurd h.symm (cen_AQ hF (hlt t)).1
      · exact absurd h.symm (cen_BQ hF (hlt t)).1
    · have := ((pair_QQ hF (hlt t) (hlt t')).1).1 h
      obtain ⟨rfl, rfl, h3⟩ := this
      rw [Fin.ext h3]
  · rintro (u | ⟨i, j, t⟩) (v | ⟨i', j', t'⟩)
    · rcases u with i | j <;> rcases v with i' | j'
      · simp only [fmap]; exact iff_of_false (cen_AA hF i i').2 (R_inl_inl _ _ _ _)
      · simp only [fmap]; exact iff_of_false (cen_AB hF i j').2 (R_inl_inl _ _ _ _)
      · simp only [fmap]
        exact iff_of_false (fun h => (cen_AB hF i' j).2 h.symm) (R_inl_inl _ _ _ _)
      · simp only [fmap]; exact iff_of_false (cen_BB hF j j').2 (R_inl_inl _ _ _ _)
    · rcases u with i | j
      · simp only [fmap]
        rw [(cen_AQ hF (hlt t')).2, R_inlA_inr]
      · simp only [fmap]
        rw [(cen_BQ hF (hlt t')).2, R_inlB_inr]
    · rcases v with i' | j'
      · simp only [fmap]
        rw [SimpleGraph.adj_comm, (cen_AQ hF (hlt t)).2, R_inr_inlA]
      · simp only [fmap]
        rw [SimpleGraph.adj_comm, (cen_BQ hF (hlt t)).2, R_inr_inlB]
    · simp only [fmap]
      rw [(pair_QQ hF (hlt t) (hlt t')).2, R_inr_inr]


/-- the frame data in terms of abstract "containers" `inA`, `inB` of the two fan sides -/
structure Pre (G : SimpleGraph V) (m ℓA ℓB n : ℕ) (bA bB : Bool) (cA cB : Fin m → V)
    (PA PB pp : Fin m → Fin m → ℕ → V) (inA inB : Fin m → V → Prop) : Prop where
  hA : 1 ≤ ℓA
  hB : 1 ≤ ℓB
  hn : 4 ≤ n
  a0 : ∀ i j, PA i j 0 = cA i
  a1 : ∀ i j s, s ≤ ℓA → ∀ t, t ≤ ℓA → PA i j s = PA i j t → s = t
  a2 : ∀ i j s t, s ≤ ℓA → t ≤ ℓA → (G.Adj (PA i j s) (PA i j t) ↔ (s + 1 = t ∨ t + 1 = s))
  a3 : ∀ i j j', j ≠ j' → ∀ s t, 1 ≤ s → s ≤ ℓA → 1 ≤ t → t ≤ ℓA → PA i j s ≠ PA i j' t
  a4 : ∀ i j j', j ≠ j' → ∀ s t, 1 ≤ s → s ≤ ℓA → 1 ≤ t → t ≤ ℓA →
    (G.Adj (PA i j s) (PA i j' t) ↔ (bA = true ∧ s = 1 ∧ t = 1))
  b0 : ∀ j i, PB j i 0 = cB j
  b1 : ∀ j i s, s ≤ ℓB → ∀ t, t ≤ ℓB → PB j i s = PB j i t → s = t
  b2 : ∀ j i s t, s ≤ ℓB → t ≤ ℓB → (G.Adj (PB j i s) (PB j i t) ↔ (s + 1 = t ∨ t + 1 = s))
  b3 : ∀ j i i', i ≠ i' → ∀ s t, 1 ≤ s → s ≤ ℓB → 1 ≤ t → t ≤ ℓB → PB j i s ≠ PB j i' t
  b4 : ∀ j i i', i ≠ i' → ∀ s t, 1 ≤ s → s ≤ ℓB → 1 ≤ t → t ≤ ℓB →
    (G.Adj (PB j i s) (PB j i' t) ↔ (bB = true ∧ s = 1 ∧ t = 1))
  mm : ∀ i j i' j', (i ≠ i' ∨ j ≠ j') → ∀ u u', 1 ≤ u → u ≤ n - 1 → 1 ≤ u' → u' ≤ n - 1 →
    pp i j u ≠ pp i' j' u' ∧ ¬ G.Adj (pp i j u) (pp i' j' u')
  ms1 : ∀ i j u u', 1 ≤ u → u ≤ n - 1 → 1 ≤ u' → u' ≤ n - 1 → pp i j u = pp i j u' → u = u'
  ms2 : ∀ i j u u', 1 ≤ u → u ≤ n - 1 → 1 ≤ u' → u' ≤ n - 1 →
    (G.Adj (pp i j u) (pp i j u') ↔ (u + 1 = u' ∨ u' + 1 = u))
  l1 : ∀ i j, PA i j ℓA = pp i j 1
  l2 : ∀ i j, PB j i ℓB = pp i j (n - 1)
  pa_in : ∀ i j s, s ≤ ℓA → inA i (PA i j s)
  pb_in : ∀ j i s, s ≤ ℓB → inB j (PB j i s)
  sA : ∀ i i', i ≠ i' → ∀ v v', inA i v → inA i' v' → v ≠ v' ∧ ¬ G.Adj v v'
  sB : ∀ j j', j ≠ j' → ∀ v v', inB j v → inB j' v' → v ≠ v' ∧ ¬ G.Adj v v'
  sAB : ∀ i j v v', inA i v → inB j v' → v ≠ v' ∧ ¬ G.Adj v v'
  sAM : ∀ i i', i ≠ i' → ∀ v, inA i v → ∀ j' u, 2 ≤ u → u ≤ n - 2 →
    v ≠ pp i' j' u ∧ ¬ G.Adj v (pp i' j' u)
  sBM : ∀ j j', j ≠ j' → ∀ v, inB j v → ∀ i' u, 2 ≤ u → u ≤ n - 2 →
    v ≠ pp i' j' u ∧ ¬ G.Adj v (pp i' j' u)
  clsA : ∀ i v, inA i v →
    ((∀ j' u, 1 ≤ u → u ≤ n - 2 → v ≠ pp i j' u) ∧
      (∀ j' u, 2 ≤ u → u ≤ n - 2 → ¬ G.Adj v (pp i j' u))) ∨ ∃ j'', v = pp i j'' 1
  clsB : ∀ j v, inB j v →
    ((∀ i' u, 2 ≤ u → u ≤ n - 1 → v ≠ pp i' j u) ∧
      (∀ i' u, 2 ≤ u → u ≤ n - 2 → ¬ G.Adj v (pp i' j u))) ∨ ∃ i'', v = pp i'' j (n - 1)

theorem Pre.toFrame {inA inB : Fin m → V → Prop}
    (h : Pre G m ℓA ℓB n bA bB cA cB PA PB pp inA inB) :
    Frame G m ℓA ℓB n bA bB cA cB PA PB pp := by
  have hA := h.hA
  have hB := h.hB
  have hn := h.hn
  have PA_leaf : ∀ i j j' s, s ≤ ℓA → PA i j s = PA i j' ℓA → j = j' ∧ s = ℓA := by
    intro i j j' s hs e
    by_cases hj : j = j'
    · subst hj; exact ⟨rfl, h.a1 i j s hs ℓA le_rfl e⟩
    · exfalso
      rcases Nat.eq_zero_or_pos s with h0 | h0
      · subst h0
        rw [h.a0, ← h.a0 i j'] at e
        have := h.a1 i j' 0 (by omega) ℓA le_rfl e
        omega
      · exact h.a3 i j j' hj s ℓA h0 hs hA le_rfl e
  have PB_leaf : ∀ j i i' s, s ≤ ℓB → PB j i s = PB j i' ℓB → i = i' ∧ s = ℓB := by
    intro j i i' s hs e
    by_cases hi : i = i'
    · subst hi; exact ⟨rfl, h.b1 j i s hs ℓB le_rfl e⟩
    · exfalso
      rcases Nat.eq_zero_or_pos s with h0 | h0
      · subst h0
        rw [h.b0, ← h.b0 j i'] at e
        have := h.b1 j i' 0 (by omega) ℓB le_rfl e
        omega
      · exact h.b3 j i i' hi s ℓB h0 hs hB le_rfl e
  have am1 : ∀ i j j' s u, s ≤ ℓA → 2 ≤ u → u ≤ n - 2 →
      PA i j s ≠ pp i j' u ∧ (G.Adj (PA i j s) (pp i j' u) ↔ (j = j' ∧ s = ℓA ∧ u = 2)) := by
    intro i j j' s u hs hu1 hu2
    have hin := h.pa_in i j s hs
    rcases h.clsA i _ hin with ⟨h1, h2⟩ | ⟨j'', hj''⟩
    · refine ⟨h1 j' u (by omega) hu2, ⟨fun hadj => absurd hadj (h2 j' u hu1 hu2), ?_⟩⟩
      rintro ⟨rfl, hs', -⟩
      exact absurd (by rw [← h.l1 i j, ← hs']) (h1 j 1 le_rfl (by omega))
    · by_cases hjj : j'' = j'
      · subst hjj
        refine ⟨?_, ?_⟩
        · rw [hj'']
          intro e
          have := h.ms1 i j'' 1 u le_rfl (by omega) (by omega) (by omega) e
          omega
        · rw [hj'', h.ms2 i j'' 1 u le_rfl (by omega) (by omega) (by omega)]
          constructor
          · rintro (e | e)
            · obtain ⟨e1, e2⟩ := PA_leaf i j j'' s hs (hj''.trans (h.l1 i j'').symm)
              exact ⟨e1, e2, by omega⟩
            · omega
          · rintro ⟨-, -, hu⟩; left; omega
      · have := h.mm i j'' i j' (Or.inr hjj) 1 u le_rfl (by omega) (by omega) (by omega)
        refine ⟨hj'' ▸ this.1, ⟨fun hadj => (this.2 (hj'' ▸ hadj)).elim, ?_⟩⟩
        rintro ⟨rfl, hs', -⟩
        subst hs'
        exact absurd (hj''.symm.trans (h.l1 i j)) (h.mm i j'' i j (Or.inr hjj) 1 1 le_rfl (by omega) le_rfl (by omega)).1
  have bm1 : ∀ j i i' s u, s ≤ ℓB → 2 ≤ u → u ≤ n - 2 →
      PB j i s ≠ pp i' j u ∧ (G.Adj (PB j i s) (pp i' j u) ↔ (i = i' ∧ s = ℓB ∧ u = n - 2)) := by
    intro j i i' s u hs hu1 hu2
    have hin := h.pb_in j i s hs
    rcases h.clsB j _ hin with ⟨h1, h2⟩ | ⟨i'', hi''⟩
    · refine ⟨h1 i' u hu1 (by omega), ⟨fun hadj => absurd hadj (h2 i' u hu1 hu2), ?_⟩⟩
      rintro ⟨rfl, hs', -⟩
      exact absurd (by rw [← h.l2 i j, ← hs']) (h1 i (n - 1) (by omega) le_rfl)
    · by_cases hii : i'' = i'
      · subst hii
        refine ⟨?_, ?_⟩
        · rw [hi'']
          intro e
          have := h.ms1 i'' j (n - 1) u (by omega) le_rfl (by omega) (by omega) e
          omega
        · rw [hi'', h.ms2 i'' j (n - 1) u (by omega) le_rfl (by omega) (by omega)]
          constructor
          · rintro (e | e)
            · omega
            · obtain ⟨e1, e2⟩ := PB_leaf j i i'' s hs (hi''.trans (h.l2 i'' j).symm)
              exact ⟨e1, e2, by omega⟩
          · rintro ⟨-, -, hu⟩; right; omega
      · have := h.mm i'' j i' j (Or.inl hii) (n - 1) u (by omega) le_rfl (by omega) (by omega)
        refine ⟨hi'' ▸ this.1, ⟨fun hadj => (this.2 (hi'' ▸ hadj)).elim, ?_⟩⟩
        rintro ⟨rfl, hs', -⟩
        subst hs'
        exact absurd (hi''.symm.trans (h.l2 i j)) (h.mm i'' j i j (Or.inl hii) (n - 1) (n - 1) (by omega) le_rfl (by omega) le_rfl).1
  exact {
    hA := hA, hB := hB, hn := hn, a0 := h.a0, a1 := h.a1, a2 := h.a2, a3 := h.a3, a4 := h.a4,
    b0 := h.b0, b1 := h.b1, b2 := h.b2, b3 := h.b3, b4 := h.b4,
    aa := fun i i' hi j j' s t hs ht => h.sA i i' hi _ _ (h.pa_in i j s hs) (h.pa_in i' j' t ht),
    bb := fun j j' hj i i' s t hs ht => h.sB j j' hj _ _ (h.pb_in j i s hs) (h.pb_in j' i' t ht),
    ab := fun i j j' i' s t hs ht => h.sAB i j' _ _ (h.pa_in i j s hs) (h.pb_in j' i' t ht),
    mm := h.mm, ms1 := h.ms1, ms2 := h.ms2, l1 := h.l1, l2 := h.l2,
    am1 := am1,
    am2 := fun i i' hi j j' s u hs hu1 hu2 => h.sAM i i' hi _ (h.pa_in i j s hs) j' u hu1 hu2,
    bm1 := bm1,
    bm2 := fun j j' hj i i' s u hs hu1 hu2 => h.sBM j j' hj _ (h.pb_in j i s hs) i' u hu1 hu2 }

end frame

end FatFlat.Dev.L66Frame
end

section
set_option autoImplicit false

namespace FatFlat.Dev.L66Model
open FatFlat.Hereditary FatFlat.Dev.L66Pat FatFlat.Dev.L66Path FatFlat.Dev.L66Walk
  FatFlat.Dev.L66Ext FatFlat.Dev.L66Half FatFlat.Dev.L66Frame

variable {V : Type} {G : SimpleGraph V} {M d : ℕ}

/-- `v` is in the `A`-branch set of row `i` or in an `S¹`-branch set of row `i` -/
def LA (C : Ctx G M d) (i : Fin M) (v : V) : Prop :=
  v ∈ C.B (aL M i) ∨ ∃ j0, v ∈ C.B (sL M i j0 0)

def LB (C : Ctx G M d) (j : Fin M) (v : V) : Prop :=
  v ∈ C.B (bL M j) ∨ ∃ i0, v ∈ C.B (sL M i0 j 2)

def LM (C : Ctx G M d) (i j : Fin M) (v : V) : Prop := ∃ t, v ∈ C.B (sL M i j t)

theorem sepAA (C : Ctx G M d) {i i' : Fin M} (hi : i ≠ i') {v v' : V} (hv : LA C i v)
    (hv' : LA C i' v') : v ≠ v' ∧ ¬ G.Adj v v' := by
  rcases hv with h | ⟨j0, h⟩ <;> rcases hv' with h' | ⟨j1, h'⟩ <;>
    exact C.sep h h' (by simp [hi, hi.symm]) (by simp [KG_inl_inl, KG_inl_inr, KG_inr_inl, KG_inr_inr, hi, hi.symm])

theorem sepBB (C : Ctx G M d) {j j' : Fin M} (hj : j ≠ j') {v v' : V} (hv : LB C j v)
    (hv' : LB C j' v') : v ≠ v' ∧ ¬ G.Adj v v' := by
  rcases hv with h | ⟨j0, h⟩ <;> rcases hv' with h' | ⟨j1, h'⟩ <;>
    exact C.sep h h' (by simp [hj, hj.symm]) (by simp [KG_inl_inl, KG_inl_inr, KG_inr_inl, KG_inr_inr, hj, hj.symm])

theorem sepAB (C : Ctx G M d) (i j : Fin M) {v v' : V} (hv : LA C i v) (hv' : LB C j v') :
    v ≠ v' ∧ ¬ G.Adj v v' := by
  rcases hv with h | ⟨j0, h⟩ <;> rcases hv' with h' | ⟨i1, h'⟩ <;>
    exact C.sep h h' (by simp) (by simp [KG_inl_inl, KG_inl_inr, KG_inr_inl, KG_inr_inr])

theorem sepAM (C : Ctx G M d) {i i' : Fin M} (hi : i ≠ i') (j' : Fin M) {v v' : V} (hv : LA C i v)
    (hv' : LM C i' j' v') : v ≠ v' ∧ ¬ G.Adj v v' := by
  obtain ⟨t, h'⟩ := hv'
  rcases hv with h | ⟨j0, h⟩ <;>
    exact C.sep h h' (by simp [hi]) (by simp [KG_inl_inr, KG_inr_inr, hi])

theorem sepBM (C : Ctx G M d) {j j' : Fin M} (hj : j ≠ j') (i' : Fin M) {v v' : V} (hv : LB C j v)
    (hv' : LM C i' j' v') : v ≠ v' ∧ ¬ G.Adj v v' := by
  obtain ⟨t, h'⟩ := hv'
  rcases hv with h | ⟨i0, h⟩ <;>
    exact C.sep h h' (by simp [hj]) (by simp [KG_inl_inr, KG_inr_inr, hj])

theorem sepMM (C : Ctx G M d) {i j i' j' : Fin M} (hij : i ≠ i' ∨ j ≠ j') {v v' : V}
    (hv : LM C i j v) (hv' : LM C i' j' v') : v ≠ v' ∧ ¬ G.Adj v v' := by
  obtain ⟨t, h⟩ := hv
  obtain ⟨t', h'⟩ := hv'
  refine C.sep h h' ?_ ?_
  · intro e; simp at e; tauto
  · rw [KG_inr_inr]; intro e; tauto


section pre
variable {nn : Fin M → Fin M → ℕ} {pq : Fin M → Fin M → ℕ → V}

theorem pre_of_model (C : Ctx G M d) (hpath : ∀ i j, PathData C i j (nn i j) (pq i j))
    {m n ℓA ℓB : ℕ} {bA bB : Bool} (σ τ : Fin m → Fin M)
    (hσ : Function.Injective σ) (hτ : Function.Injective τ)
    (hn : ∀ i j, nn (σ i) (τ j) = n) (hfour : 4 ≤ n) (hℓA : 1 ≤ ℓA) (hℓB : 1 ≤ ℓB)
    (cA' cB' : Fin M → V) (PA' PB' : Fin M → V → ℕ → V)
    (hFA : ∀ i, Fan G ℓA bA (cA' (σ i)) ((fun j0 => pq (σ i) j0 1) '' Set.range τ) (PA' (σ i)))
    (hFB : ∀ j, Fan G ℓB bB (cB' (τ j))
      ((fun i0 => pq i0 (τ j) (nn i0 (τ j) - 1)) '' Set.range σ) (PB' (τ j)))
    (hAin : ∀ i, ∀ x ∈ (fun j0 => pq (σ i) j0 1) '' Set.range τ, ∀ s ≤ ℓA,
      PA' (σ i) x s ∈ C.B (aL M (σ i)) ∨ ∃ j0, PA' (σ i) x s = pq (σ i) j0 1)
    (hBin : ∀ j, ∀ x ∈ (fun i0 => pq i0 (τ j) (nn i0 (τ j) - 1)) '' Set.range σ, ∀ s ≤ ℓB,
      PB' (τ j) x s ∈ C.B (bL M (τ j)) ∨ ∃ i0, PB' (τ j) x s = pq i0 (τ j) (nn i0 (τ j) - 1)) :
    Pre G m ℓA ℓB n bA bB (fun i => cA' (σ i)) (fun j => cB' (τ j))
      (fun i j s => PA' (σ i) (pq (σ i) (τ j) 1) s)
      (fun j i s => PB' (τ j) (pq (σ i) (τ j) (nn (σ i) (τ j) - 1)) s)
      (fun i j u => pq (σ i) (τ j) u)
      (fun i v => v ∈ C.B (aL M (σ i)) ∨ ∃ j0, v = pq (σ i) j0 1)
      (fun j v => v ∈ C.B (bL M (τ j)) ∨ ∃ i0, v = pq i0 (τ j) (nn i0 (τ j) - 1)) := by
  have hx1 : ∀ i j, pq i j 1 ∈ C.B (sL M i j 0) := fun i j => (hpath i j).x
  have hy1 : ∀ i j, pq i j (nn i j - 1) ∈ C.B (sL M i j 2) := fun i j => (hpath i j).y
  have hmid : ∀ i j u, 1 ≤ u → u ≤ nn i j - 1 → LM C i j (pq i j u) :=
    fun i j u h1 h2 => (hpath i j).mid u h1 h2
  have hmid' : ∀ i j u, 1 ≤ u → u ≤ n - 1 → LM C (σ i) (τ j) (pq (σ i) (τ j) u) := by
    intro i j u h1 h2
    exact hmid _ _ u h1 (by rw [hn]; exact h2)
  have hsh : ∀ i j, Shortest G (C.U (σ i) (τ j)) (C.B (aL M (σ i))) (C.B (bL M (τ j))) n
      (pq (σ i) (τ j)) := by
    intro i j
    have := (hpath (σ i) (τ j)).sh
    rwa [hn] at this
  have toLA : ∀ i v, (v ∈ C.B (aL M (σ i)) ∨ ∃ j0, v = pq (σ i) j0 1) → LA C (σ i) v := by
    rintro i v (h | ⟨j0, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j0, hx1 _ _⟩
  have toLB : ∀ j v, (v ∈ C.B (bL M (τ j)) ∨ ∃ i0, v = pq i0 (τ j) (nn i0 (τ j) - 1)) →
      LB C (τ j) v := by
    rintro j v (h | ⟨i0, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i0, hy1 _ _⟩
  have leafA : ∀ i j, pq (σ i) (τ j) 1 ∈ (fun j0 => pq (σ i) j0 1) '' Set.range τ :=
    fun i j => ⟨τ j, ⟨j, rfl⟩, rfl⟩
  have leafB : ∀ j i, pq (σ i) (τ j) (nn (σ i) (τ j) - 1) ∈
      (fun i0 => pq i0 (τ j) (nn i0 (τ j) - 1)) '' Set.range σ :=
    fun j i => ⟨σ i, ⟨i, rfl⟩, rfl⟩
  have neA : ∀ i j j', j ≠ j' → pq (σ i) (τ j) 1 ≠ pq (σ i) (τ j') 1 := by
    intro i j j' hj
    exact (sepMM C (Or.inr (fun e => hj (hτ e))) (hmid' i j 1 le_rfl (by omega))
      (hmid' i j' 1 le_rfl (by omega))).1
  have neB : ∀ j i i', i ≠ i' → pq (σ i) (τ j) (nn (σ i) (τ j) - 1) ≠
      pq (σ i') (τ j) (nn (σ i') (τ j) - 1) := by
    intro j i i' hi
    rw [hn, hn]
    exact (sepMM C (Or.inl (fun e => hi (hσ e))) (hmid' i j (n - 1) (by omega) le_rfl)
      (hmid' i' j (n - 1) (by omega) le_rfl)).1
  refine
    { hA := hℓA, hB := hℓB, hn := hfour
      a0 := fun i j => (hFA i).start _ (leafA i j)
      a1 := fun i j s hs t ht e => (hFA i).inj _ (leafA i j) s hs t ht e
      a2 := fun i j s t hs ht => (hFA i).adj _ (leafA i j) s hs t ht
      a3 := fun i j j' hj s t hs1 hs2 ht1 ht2 =>
        (hFA i).disj _ (leafA i j) _ (leafA i j') (neA i j j' hj) s t hs1 hs2 ht1 ht2
      a4 := fun i j j' hj s t hs1 hs2 ht1 ht2 =>
        (hFA i).link _ (leafA i j) _ (leafA i j') (neA i j j' hj) s t hs1 hs2 ht1 ht2
      b0 := fun j i => (hFB j).start _ (leafB j i)
      b1 := fun j i s hs t ht e => (hFB j).inj _ (leafB j i) s hs t ht e
      b2 := fun j i s t hs ht => (hFB j).adj _ (leafB j i) s hs t ht
      b3 := fun j i i' hi s t hs1 hs2 ht1 ht2 =>
        (hFB j).disj _ (leafB j i) _ (leafB j i') (neB j i i' hi) s t hs1 hs2 ht1 ht2
      b4 := fun j i i' hi s t hs1 hs2 ht1 ht2 =>
        (hFB j).link _ (leafB j i) _ (leafB j i') (neB j i i' hi) s t hs1 hs2 ht1 ht2
      mm := ?_, ms1 := ?_, ms2 := ?_
      l1 := fun i j => (hFA i).finish _ (leafA i j)
      l2 := fun i j => by
        have := (hFB j).finish _ (leafB j i)
        rw [this, hn]
      pa_in := fun i j s hs => hAin i _ (leafA i j) s hs
      pb_in := fun j i s hs => hBin j _ (leafB j i) s hs
      sA := ?_, sB := ?_, sAB := ?_, sAM := ?_, sBM := ?_, clsA := ?_, clsB := ?_ }
  · intro i j i' j' hij u u' hu1 hu2 hu1' hu2'
    have hij' : σ i ≠ σ i' ∨ τ j ≠ τ j' := by
      rcases hij with h | h
      · exact Or.inl (fun e => h (hσ e))
      · exact Or.inr (fun e => h (hτ e))
    exact sepMM C hij' (hmid' i j u hu1 hu2) (hmid' i' j' u' hu1' hu2')
  · intro i j u u' hu1 hu2 hu1' hu2' e
    rcases lt_trichotomy u u' with h | h | h
    · exact absurd e ((hsh i j).inj u (by omega) u' (by omega) h)
    · exact h
    · exact absurd e.symm ((hsh i j).inj u' (by omega) u (by omega) h)
  · intro i j u u' hu1 hu2 hu1' hu2'
    constructor
    · intro hadj
      by_contra hnot
      push_neg at hnot
      rcases lt_trichotomy u u' with h | h | h
      · exact (hsh i j).chord u (by omega) u' (by omega) (by omega) hadj
      · subst h; exact G.loopless.irrefl _ hadj
      · exact (hsh i j).chord u' (by omega) u (by omega) (by omega) hadj.symm
    · rintro (rfl | rfl)
      · exact (hsh i j).good.2.2.2 u (by omega)
      · exact ((hsh i j).good.2.2.2 u' (by omega)).symm
  · intro i i' hi v v' hv hv'
    exact sepAA C (fun e => hi (hσ e)) (toLA i v hv) (toLA i' v' hv')
  · intro j j' hj v v' hv hv'
    exact sepBB C (fun e => hj (hτ e)) (toLB j v hv) (toLB j' v' hv')
  · intro i j v v' hv hv'
    exact sepAB C (σ i) (τ j) (toLA i v hv) (toLB j v' hv')
  · intro i i' hi v hv j' u hu1 hu2
    exact sepAM C (fun e => hi (hσ e)) (τ j') (toLA i v hv) (hmid' i' j' u (by omega) (by omega))
  · intro j j' hj v hv i' u hu1 hu2
    exact sepBM C (fun e => hj (hτ e)) (σ i') (toLB j v hv) (hmid' i' j' u (by omega) (by omega))
  · intro i v hv
    rcases hv with hv | ⟨j0, rfl⟩
    · left
      refine ⟨fun j' u hu1 hu2 e => ?_, fun j' u hu1 hu2 => ?_⟩
      · obtain ⟨t, ht⟩ := hmid' i j' u hu1 (by omega)
        have := C.uniq hv (e ▸ ht)
        simp at this
      · exact (hsh i j').nbX v hv u hu1 (by omega)
    · by_cases hj0 : ∃ j'', τ j'' = j0
      · obtain ⟨j'', rfl⟩ := hj0
        exact Or.inr ⟨j'', rfl⟩
      · left
        push_neg at hj0
        refine ⟨fun j' u hu1 hu2 => ?_, fun j' u hu1 hu2 => ?_⟩
        · exact (sepMM C (Or.inr (fun e => hj0 j' e.symm)) ⟨0, hx1 _ _⟩
            (hmid' i j' u hu1 (by omega))).1
        · exact (sepMM C (Or.inr (fun e => hj0 j' e.symm)) ⟨0, hx1 _ _⟩
            (hmid' i j' u (by omega) (by omega))).2
  · intro j v hv
    rcases hv with hv | ⟨i0, rfl⟩
    · left
      refine ⟨fun i' u hu1 hu2 e => ?_, fun i' u hu1 hu2 => ?_⟩
      · obtain ⟨t, ht⟩ := hmid' i' j u (by omega) hu2
        have := C.uniq hv (e ▸ ht)
        simp at this
      · exact (hsh i' j).nbY v hv u (by omega)
    · by_cases hi0 : ∃ i'', σ i'' = i0
      · obtain ⟨i'', rfl⟩ := hi0
        refine Or.inr ⟨i'', ?_⟩
        rw [hn]
      · left
        push_neg at hi0
        refine ⟨fun i' u hu1 hu2 => ?_, fun i' u hu1 hu2 => ?_⟩
        · exact (sepMM C (Or.inl (fun e => hi0 i' e.symm)) ⟨2, hy1 _ _⟩
            (hmid' i' j u (by omega) hu2)).1
        · exact (sepMM C (Or.inl (fun e => hi0 i' e.symm)) ⟨2, hy1 _ _⟩
            (hmid' i' j u (by omega) (by omega))).2

end pre

end FatFlat.Dev.L66Model
end

section
set_option autoImplicit false

namespace FatFlat.Dev.L66Main
open FatFlat.Hereditary FatFlat.Dev.Emb FatFlat.Dev.L66Pat FatFlat.Dev.L66Path FatFlat.Dev.L66Walk
  FatFlat.Dev.L66Ext FatFlat.Dev.L66Half FatFlat.Dev.L66Frame FatFlat.Dev.L66Model
  FatFlat.Dev.L66Comb

variable {V : Type}

theorem psi_surj (M : ℕ) : Function.Surjective (psi M M 2) := by
  rintro (w | ⟨i, j, t⟩)
  · exact ⟨Sum.inl w, rfl⟩
  · exact ⟨Sum.inr ⟨edgeOf i j, pos (BG M M) 2 (edgeOf i j) (Sum.inl i) t⟩, by
      rw [psi_inr, pos_pos]⟩

theorem ctx_of_model (G : SimpleGraph V) (M d : ℕ)
    (B : (Fin M ⊕ Fin M) ⊕ (Σ _ : (BG M M).edgeSet, Fin (2 + 1)) → Set V)
    (hdisj : ∀ u w, u ≠ w → Disjoint (B u) (B w))
    (hadj : ∀ u w, u ≠ w → ((∃ x ∈ B u, ∃ y ∈ B w, G.Adj x y) ↔ (SD (BG M M) 2).Adj u w))
    (hrad : ∀ w, RadiusLE G (B w) d) : Nonempty (Ctx G M d) := by
  choose chi hchi using psi_surj M
  refine ⟨{ B := fun u => B (chi u), disj := ?_, adj_iff := ?_, rad := fun w => hrad _ }⟩
  · intro u w huw
    apply hdisj
    intro e
    apply huw
    rw [← hchi u, ← hchi w, e]
  · intro u w huw
    have hne : chi u ≠ chi w := by
      intro e; apply huw; rw [← hchi u, ← hchi w, e]
    rw [hadj _ _ hne, psi_adj, hchi, hchi]

theorem ctx_of_minor (G : SimpleGraph V) (M d : ℕ)
    (h : IsShallowInducedMinor (subdividedBiclique 3 M M) G d) : Nonempty (Ctx G M d) := by
  obtain ⟨M', hM'⟩ := h
  exact ctx_of_model G M d M'.B M'.disjoint (fun u w huw => M'.adj_iff u w huw) hM'

theorem emb_zero {V : Type} (G : SimpleGraph V) (r : ℕ) :
    Nonempty (subdividedBiclique r 0 0 ↪g G) := by
  have : IsEmpty ((Fin 0 ⊕ Fin 0) ⊕ (Σ _ : (BG 0 0).edgeSet, Fin (r - 1 + 1))) := by
    refine ⟨?_⟩
    rintro (w | ⟨e, t⟩)
    · rcases w with w | w <;> exact w.elim0
    · obtain ⟨⟨i, j⟩, rfl⟩ := edge_cases e
      exact i.elim0
  exact ⟨⟨⟨fun x => isEmptyElim x, fun a => isEmptyElim a⟩, fun {a} => isEmptyElim a⟩⟩


theorem main_ext (d m : ℕ) : ∃ M : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    Nonempty (Ctx G M d) →
    ∃ r : ℕ, 3 ≤ r ∧ r ≤ 8 * d + 3 ∧
      (Nonempty (subdividedBiclique r m m ↪g G) ∨ Nonempty (biweb r m m ↪g G) ∨
        Nonempty (mixweb r m m ↪g G)) := by
  classical
  obtain ⟨Nf, hNf⟩ := half d
  obtain ⟨M₁, M₂, hbic⟩ := biclique_mono (6 * d + 5)
    (((d + 2) * 2) * (Nf (((d + 2) * 2) * (m - 1) + 1) m - 1) + 1)
    (Nf (((d + 2) * 2) * (Nf (((d + 2) * 2) * (m - 1) + 1) m - 1) + 1) (((d + 2) * 2) * (m - 1) + 1))
  refine ⟨max M₁ M₂, ?_⟩
  intro V _ G ⟨C⟩
  by_cases hm : m = 0
  · subst hm
    exact ⟨3, le_rfl, by omega, Or.inl (emb_zero G 3)⟩
  generalize hM : max M₁ M₂ = M at C
  set T := (d + 2) * 2 with hT
  set mJ := T * (m - 1) + 1 with hmJ
  set mI1 := Nf mJ m with hmI1
  set R := T * (mI1 - 1) + 1 with hR
  set mJ0 := Nf R mJ with hmJ0
  -- path data
  choose nn pq hpath using C.path_exists
  -- constant path length on a large biclique
  obtain ⟨I0, -, J0, -, hI0, hJ0, n, hn0⟩ := hbic (Fin M) (Fin M) Finset.univ Finset.univ nn
    (fun i j => by have := (hpath i j).le; omega)
    (by simp; omega) (by simp; omega)
  -- A side
  let Ap : Fin M → Set V := fun i => C.B (aL M i) ∪ Set.range (fun j0 => pq i j0 1)
  choose zc hzc using fun i : Fin M => C.rad (aL M i)
  have hx1 : ∀ i j, pq i j 1 ∈ C.B (sL M i j 0) := fun i j => (hpath i j).x
  have hy1 : ∀ i j, pq i j (nn i j - 1) ∈ C.B (sL M i j 2) := fun i j => (hpath i j).y
  have hinjA : ∀ i, Function.Injective (fun j0 => pq i j0 1) := by
    intro i j0 j1 e
    have := C.uniq (hx1 i j0) (by rw [show pq i j0 1 = pq i j1 1 from e]; exact hx1 i j1)
    simpa using this
  have hdA : ∀ (i j0 : Fin M),
      (G.induce (Ap i)).edist ⟨(zc i).val, Or.inl (zc i).2⟩ ⟨pq i j0 1, Or.inr ⟨j0, rfl⟩⟩ ≤
        ((d + 1 : ℕ) : ℕ∞) := by
    intro i j0
    exact edist_leaf (S := C.B (aL M i)) (S' := Ap i) Set.subset_union_left (zc i).2 (hzc i)
      (a := pq i j0 0) (hpath i j0).sh.good.1 _
      ((hpath i j0).sh.good.2.2.2 0 (by have := (hpath i j0).four; omega))
  obtain ⟨J1, hJ1sub, hJ1card, hA⟩ := hNf V G (Fin M) (Fin M) Ap (fun i => (zc i).val)
    (fun i j0 => pq i j0 1) (fun i => Or.inl (zc i).2) (fun i j0 => Or.inr ⟨j0, rfl⟩) hinjA hdA R mJ
    I0 J0 (le_of_eq hI0) (le_of_eq hJ0.symm)
  haveI : Nonempty V := by
    obtain ⟨i, -⟩ := Finset.card_pos.1 (by omega : 0 < I0.card)
    exact ⟨(zc i).val⟩
  choose! ℓf bf hℓf cf Pf hfan hcm hPm using hA
  have hg : ∀ i ∈ I0, (ℓf i, bf i) ∈ (Finset.range (d + 2)) ×ˢ (Finset.univ : Finset Bool) := by
    intro i hi
    exact Finset.mem_product.2 ⟨Finset.mem_range.2 (by have := hℓf i hi; omega), Finset.mem_univ _⟩
  obtain ⟨I1, hI1sub, hI1card, ⟨ℓA, bA⟩, hyA, hconstA⟩ := pigeon mI1 I0 (fun i => (ℓf i, bf i))
    ((Finset.range (d + 2)) ×ˢ (Finset.univ : Finset Bool)) hg (by
      rw [Finset.card_product, Finset.card_range, hI0]
      simp [hT, hR])
  -- B side
  let Bp : Fin M → Set V := fun j => C.B (bL M j) ∪ Set.range (fun i0 => pq i0 j (nn i0 j - 1))
  choose zd hzd using fun j : Fin M => C.rad (bL M j)
  have hinjB : ∀ j, Function.Injective (fun i0 => pq i0 j (nn i0 j - 1)) := by
    intro j i0 i1 e
    have := C.uniq (hy1 i0 j) (by rw [show pq i0 j (nn i0 j - 1) = pq i1 j (nn i1 j - 1) from e]; exact hy1 i1 j)
    simpa using this
  have hdB : ∀ (j i0 : Fin M),
      (G.induce (Bp j)).edist ⟨(zd j).val, Or.inl (zd j).2⟩
        ⟨pq i0 j (nn i0 j - 1), Or.inr ⟨i0, rfl⟩⟩ ≤ ((d + 1 : ℕ) : ℕ∞) := by
    intro j i0
    have hfour := (hpath i0 j).four
    have hadj := (hpath i0 j).sh.good.2.2.2 (nn i0 j - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega)] at hadj
    exact edist_leaf (S := C.B (bL M j)) (S' := Bp j) Set.subset_union_left (zd j).2 (hzd j)
      (a := pq i0 j (nn i0 j)) (hpath i0 j).sh.good.2.1 _ hadj.symm
  obtain ⟨I, hIsub, hIcard, hB⟩ := hNf V G (Fin M) (Fin M) Bp (fun j => (zd j).val)
    (fun j i0 => pq i0 j (nn i0 j - 1)) (fun j => Or.inl (zd j).2) (fun j i0 => Or.inr ⟨i0, rfl⟩)
    hinjB hdB mJ m J1 I1 (le_of_eq hJ1card) (by rw [hI1card])
  choose! ℓg bg hℓg cg Pg hfanB hcmB hPmB using hB
  have hg' : ∀ j ∈ J1, (ℓg j, bg j) ∈ (Finset.range (d + 2)) ×ˢ (Finset.univ : Finset Bool) := by
    intro j hj
    exact Finset.mem_product.2 ⟨Finset.mem_range.2 (by have := hℓg j hj; omega), Finset.mem_univ _⟩
  obtain ⟨J, hJsub, hJcard, ⟨ℓB, bB⟩, hyB, hconstB⟩ := pigeon m J1 (fun j => (ℓg j, bg j))
    ((Finset.range (d + 2)) ×ˢ (Finset.univ : Finset Bool)) hg' (by
      rw [Finset.card_product, Finset.card_range, hJ1card]
      simp [hT, hmJ])
  -- indices
  let σ : Fin m ↪o Fin M := I.orderEmbOfFin hIcard
  let τ : Fin m ↪o Fin M := J.orderEmbOfFin hJcard
  have hσI : ∀ i, σ i ∈ I := fun i => Finset.orderEmbOfFin_mem I hIcard i
  have hτJ : ∀ j, τ j ∈ J := fun j => Finset.orderEmbOfFin_mem J hJcard j
  have hσI0 : ∀ i, σ i ∈ I0 := fun i => hI1sub (hIsub (hσI i))
  have hσI1 : ∀ i, σ i ∈ I1 := fun i => hIsub (hσI i)
  have hτJ0 : ∀ j, τ j ∈ J0 := fun j => hJ1sub (hJsub (hτJ j))
  have hτJ1 : ∀ j, τ j ∈ J1 := fun j => hJsub (hτJ j)
  have hn : ∀ i j, nn (σ i) (τ j) = n := fun i j => hn0 _ (hσI0 i) _ (hτJ0 j)
  have hrangeσ : Set.range σ = (I : Set (Fin M)) := by
    exact Finset.range_orderEmbOfFin I hIcard
  have hrangeτ : Set.range τ = (J : Set (Fin M)) := by
    exact Finset.range_orderEmbOfFin J hJcard
  have hℓA : ∀ i, ℓf (σ i) = ℓA ∧ bf (σ i) = bA := fun i => by
    have := hconstA (σ i) (hσI1 i)
    simpa [Prod.ext_iff] using this
  have hℓB : ∀ j, ℓg (τ j) = ℓB ∧ bg (τ j) = bB := fun j => by
    have := hconstB (τ j) (hτJ j)
    simpa [Prod.ext_iff] using this
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  let i0 : Fin m := ⟨0, hmpos⟩
  have hfour : 4 ≤ n := by
    have := (hpath (σ i0) (τ i0)).four
    rwa [hn] at this
  have hnle : n ≤ 6 * d + 4 := by
    have := (hpath (σ i0) (τ i0)).le
    rwa [hn] at this
  have hℓA1 : 1 ≤ ℓA := by
    have := (hfan (σ i0) (hσI0 i0)).one_le
    rwa [(hℓA i0).1] at this
  have hℓB1 : 1 ≤ ℓB := by
    have := (hfanB (τ i0) (hτJ1 i0)).one_le
    rwa [(hℓB i0).1] at this
  have hℓAle : ℓA ≤ d + 1 := by
    have := hℓf (σ i0) (hσI0 i0)
    rwa [(hℓA i0).1] at this
  have hℓBle : ℓB ≤ d + 1 := by
    have := hℓg (τ i0) (hτJ1 i0)
    rwa [(hℓB i0).1] at this
  have hsubA : ∀ i, (fun j0 => pq (σ i) j0 1) '' Set.range τ ⊆
      (fun j0 => pq (σ i) j0 1) '' (J1 : Set (Fin M)) := by
    intro i
    apply Set.image_mono
    rw [hrangeτ]
    exact fun j hj => hJsub hj
  have hsubB : ∀ j, (fun i0 => pq i0 (τ j) (nn i0 (τ j) - 1)) '' Set.range σ ⊆
      (fun i0 => pq i0 (τ j) (nn i0 (τ j) - 1)) '' (I : Set (Fin M)) := by
    intro j
    apply Set.image_mono
    rw [hrangeσ]
  have hFA : ∀ i, Fan G ℓA bA (cf (σ i)) ((fun j0 => pq (σ i) j0 1) '' Set.range τ) (Pf (σ i)) := by
    intro i
    have h1 := hfan (σ i) (hσI0 i)
    rw [(hℓA i).1, (hℓA i).2] at h1
    exact h1.mono (hsubA i)
  have hFB : ∀ j, Fan G ℓB bB (cg (τ j))
      ((fun i0 => pq i0 (τ j) (nn i0 (τ j) - 1)) '' Set.range σ) (Pg (τ j)) := by
    intro j
    have h1 := hfanB (τ j) (hτJ1 j)
    rw [(hℓB j).1, (hℓB j).2] at h1
    exact h1.mono (hsubB j)
  have hAin : ∀ i, ∀ x ∈ (fun j0 => pq (σ i) j0 1) '' Set.range τ, ∀ s ≤ ℓA,
      Pf (σ i) x s ∈ C.B (aL M (σ i)) ∨ ∃ j0, Pf (σ i) x s = pq (σ i) j0 1 := by
    intro i x hx s hs
    have := hPm (σ i) (hσI0 i) x (hsubA i hx) s (by rw [(hℓA i).1]; exact hs)
    rcases this with h | ⟨j0, hj0⟩
    · exact Or.inl h
    · exact Or.inr ⟨j0, hj0.symm⟩
  have hBin : ∀ j, ∀ x ∈ (fun i0 => pq i0 (τ j) (nn i0 (τ j) - 1)) '' Set.range σ, ∀ s ≤ ℓB,
      Pg (τ j) x s ∈ C.B (bL M (τ j)) ∨ ∃ i1, Pg (τ j) x s = pq i1 (τ j) (nn i1 (τ j) - 1) := by
    intro j x hx s hs
    have := hPmB (τ j) (hτJ1 j) x (hsubB j hx) s (by rw [(hℓB j).1]; exact hs)
    rcases this with h | ⟨i1, hi1⟩
    · exact Or.inl h
    · exact Or.inr ⟨i1, hi1.symm⟩
  have hpre := pre_of_model C hpath (m := m) (n := n) (ℓA := ℓA) (ℓB := ℓB) (bA := bA) (bB := bB)
    σ τ σ.injective τ.injective hn hfour hℓA1 hℓB1 cf cg Pf Pg hFA hFB hAin hBin
  obtain ⟨f, hf, hadj⟩ := frame_embed hpre.toFrame
  refine ⟨ℓA + (n - 3) + ℓB, by omega, by omega, ?_⟩
  exact emb_of_spec G (ℓA + (n - 3) + ℓB) m bA bB f hf hadj

end FatFlat.Dev.L66Main
end

section
set_option autoImplicit false

namespace FatFlat.Hereditary

open FatFlat.Dev.L66Main in
theorem chk_lemma_6_6 (d m : ℕ) : ∃ M : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    IsShallowInducedMinor (subdividedBiclique 3 M M) G d →
    ∃ r : ℕ, 3 ≤ r ∧ r ≤ 8 * d + 3 ∧
      (Nonempty (subdividedBiclique r m m ↪g G) ∨ Nonempty (biweb r m m ↪g G) ∨
        Nonempty (mixweb r m m ↪g G)) := by
  obtain ⟨M, hM⟩ := main_ext d m
  exact ⟨M, fun V _ G h => hM V G (ctx_of_minor G M d h)⟩

end FatFlat.Hereditary
end

theorem solution : type_of% @FatFlat.Hereditary.chk_lemma_6_6 := @FatFlat.Hereditary.chk_lemma_6_6
