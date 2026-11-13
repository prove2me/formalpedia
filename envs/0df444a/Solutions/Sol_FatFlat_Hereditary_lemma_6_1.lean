-- Prove2me | solution 1 for FatFlat.Hereditary.lemma_6_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:59:06.104407+00:00
-- url     : https://prove2.me/submissions/de543923-c2e6-414d-9cf4-be53cc18c9d2

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Classes
import Theorems.Thm_FatFlat_Hereditary_lemma_6_2

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

lemma mp_val (f : H →g H') (e : H.edgeSet) :
    ((f.mapEdgeSet e : H'.edgeSet) : Sym2 W') =
      s(f (Quot.out (e : Sym2 W)).1, f (Quot.out (e : Sym2 W)).2) := by
  have h := out_eq (e : Sym2 W)
  show Sym2.map f (e : Sym2 W) = _
  conv_lhs => rw [← h]
  rfl

lemma out_ne (e : H.edgeSet) : (Quot.out (e : Sym2 W)).1 ≠ (Quot.out (e : Sym2 W)).2 := by
  have h := out_eq (e : Sym2 W)
  have he := e.2
  rw [← h] at he
  exact H.ne_of_adj he

/-- the induced vertex map on subdivisions -/
noncomputable def sdMap (f : H →g H') (k : ℕ) :
    (W ⊕ Σ _ : H.edgeSet, Fin (k + 1)) → (W' ⊕ Σ _ : H'.edgeSet, Fin (k + 1))
  | Sum.inl u => Sum.inl (f u)
  | Sum.inr ⟨e, i⟩ => Sum.inr ⟨f.mapEdgeSet e,
      pos H' k (f.mapEdgeSet e) (f (Quot.out (e : Sym2 W)).1) i⟩

theorem sdMap_adj (f : H →g H') (hf : Function.Injective f) (k : ℕ) (x y) :
    (SD H' k).Adj (sdMap f k x) (sdMap f k y) ↔ (SD H k).Adj x y := by
  rcases x with u | ⟨e, i⟩
  · rcases y with v | ⟨e', j⟩
    · simp [sdMap, SD_adj_inl_inl]
    · simp only [sdMap]
      rw [pos_adj_inl H' k _ _ _ (mp_val f e') (hf.ne (out_ne e')), SD_adj_inl_inr, hf.eq_iff,
        hf.eq_iff]
  · rcases y with v | ⟨e', j⟩
    · simp only [sdMap]
      rw [SimpleGraph.adj_comm, SimpleGraph.adj_comm (SD H k),
        pos_adj_inl H' k _ _ _ (mp_val f e) (hf.ne (out_ne e)), SD_adj_inl_inr, hf.eq_iff,
        hf.eq_iff]
    · simp only [sdMap]
      by_cases h : e = e'
      · subst h
        rw [pos_adj_inr, SD_adj_inr_inr]
        simp
      · have h' : f.mapEdgeSet e ≠ f.mapEdgeSet e' := fun h2 =>
          h (SimpleGraph.Hom.mapEdgeSet.injective f hf h2)
        rw [SD_adj_inr_inr, SD_adj_inr_inr]
        simp [h, h']

theorem sdMap_inj (f : H →g H') (hf : Function.Injective f) (k : ℕ) :
    Function.Injective (sdMap f k) := by
  rintro (u | ⟨e, i⟩) (v | ⟨e', j⟩) h
  · simp only [sdMap, Sum.inl.injEq] at h; rw [hf h]
  · simp [sdMap] at h
  · simp [sdMap] at h
  · simp only [sdMap, Sum.inr.injEq, Sigma.mk.inj_iff] at h
    obtain ⟨h1, h2⟩ := h
    have := SimpleGraph.Hom.mapEdgeSet.injective f hf h1
    subst this
    simp only [heq_eq_eq] at h2
    rw [pos_inj] at h2
    rw [h2]

/-- Functoriality of subdivision (constant `k`) for injective homomorphisms. -/
noncomputable def sdEmb (f : H →g H') (hf : Function.Injective f) (k : ℕ) :
    SD H k ↪g SD H' k where
  toFun := sdMap f k
  inj' := sdMap_inj f hf k
  map_rel_iff' := sdMap_adj f hf k _ _

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

lemma sdMap_pre (f : H →g H') (hf : Function.Injective f) (k : ℕ) (w' : W')
    (x : W ⊕ Σ _ : H.edgeSet, Fin (k + 1))
    (h : (SD H' k).Adj (Sum.inl w') (sdMap f k x)) : ∃ u, f u = w' := by
  rcases x with u | ⟨e, i⟩
  · exact absurd h (SD_adj_inl_inl H' k _ _)
  · simp only [sdMap] at h
    rw [pos_adj_inl H' k _ _ _ (mp_val f e) (hf.ne (out_ne e))] at h
    rcases h with ⟨h, -⟩ | ⟨h, -⟩
    · exact ⟨_, h.symm⟩
    · exact ⟨_, h.symm⟩

/-- Functoriality of the web of a subdivision, for marked principal vertices. -/
noncomputable def webSdEmbGen (f : H →g H') (hf : Function.Injective f) (k : ℕ)
    (P : Set W) (P' : Set W') (hP : ∀ u, f u ∈ P' ↔ u ∈ P) :
    webOf (SD H k) (Sum.inl '' P) ↪g webOf (SD H' k) (Sum.inl '' P') :=
  webOfEmb (sdEmb f hf k) _ _
    (by rintro _ ⟨u, hu, rfl⟩; exact ⟨f u, (hP u).2 hu, rfl⟩)
    (by
      rintro _ ⟨w', hw', rfl⟩ x y hxy ha hb
      obtain ⟨u, rfl⟩ := sdMap_pre f hf k _ x ha
      rw [webOf_adj]
      exact Or.inr ⟨hxy, Sum.inl u, ⟨u, (hP u).1 hw', rfl⟩,
        (sdMap_adj f hf k (Sum.inl u) x).1 ha, (sdMap_adj f hf k (Sum.inl u) y).1 hb⟩)

/-- Functoriality of the web of a subdivision (principal vertices). -/
noncomputable def webSdEmb (f : H →g H') (hf : Function.Injective f) (k : ℕ) :
    webOf (SD H k) (Set.range Sum.inl) ↪g webOf (SD H' k) (Set.range Sum.inl) := by
  have := webSdEmbGen f hf k Set.univ Set.univ (by simp)
  simpa [Set.image_univ] using this

/-- the inclusion `K_k ⊆ K_m` as an injective homomorphism -/
def castHom {k m : ℕ} (h : k ≤ m) : (⊤ : SimpleGraph (Fin k)) →g (⊤ : SimpleGraph (Fin m)) where
  toFun := Fin.castLE h
  map_rel' := by
    intro a b hab
    simp only [SimpleGraph.top_adj] at hab ⊢
    exact fun h' => hab (Fin.castLE_injective h h')

theorem subdividedClique_mono (r k m : ℕ) (h : k ≤ m) :
    Nonempty (subdividedClique r k ↪g subdividedClique r m) :=
  ⟨sdEmb (castHom h) (Fin.castLE_injective h) (r - 1)⟩

theorem web_mono (r k m : ℕ) (h : k ≤ m) :
    Nonempty (web r k ↪g web r m) :=
  ⟨webSdEmb (castHom h) (Fin.castLE_injective h) (r - 1)⟩

end web
end FatFlat.Dev.Emb
end

section
set_option autoImplicit false

namespace FatFlat.Hereditary
open FatFlat.Dev.Emb in
theorem chk_lemma_6_1 (C : GraphClass) (hC : PatternFree C) : ISMF C := by
  obtain ⟨R, hR⟩ := FatFlat.Hereditary.lemma_6_2
  intro d
  have hk : ∀ r : ℕ, ∃ k : ℕ, 3 ≤ r → ∀ (V : Type) [Fintype V] (G : SimpleGraph V), C V G →
      IsEmpty (subdividedClique r k ↪g G) ∧ IsEmpty (web r k ↪g G) := by
    intro r
    by_cases h : 3 ≤ r
    · obtain ⟨k, hk⟩ := hC r h
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose kf hkf using hk
  obtain ⟨n, H, hH⟩ := hR d ((Finset.range (R d + 1)).sup kf)
  refine ⟨n, H, ?_⟩
  intro V _ G hG hmin
  obtain ⟨r, hr3, hrR, hemb⟩ := hH V G hmin
  have hle : kf r ≤ (Finset.range (R d + 1)).sup kf :=
    Finset.le_sup (f := kf) (Finset.mem_range.mpr (by omega))
  obtain ⟨h1, h2⟩ := hkf r hr3 V G hG
  rcases hemb with e | e
  · obtain ⟨e0⟩ := subdividedClique_mono r (kf r) _ hle
    exact h1.false (e0.trans e.some)
  · obtain ⟨e0⟩ := web_mono r (kf r) _ hle
    exact h2.false (e0.trans e.some)
end FatFlat.Hereditary
end

theorem solution : type_of% @FatFlat.Hereditary.chk_lemma_6_1 := @FatFlat.Hereditary.chk_lemma_6_1
