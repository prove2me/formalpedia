-- Prove2me | solution 1 for FatFlat.Hereditary.lemma_6_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:39:21.481525+00:00
-- url     : https://prove2.me/submissions/dc56f667-650f-474a-a355-c5d835765b1e

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Classes
import Theorems.Thm_FatFlat_Hereditary_lemma_6_6
import Theorems.Thm_FatFlat_Hereditary_observation_1

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

end web
end FatFlat.Dev.Emb
end

section
set_option autoImplicit false

namespace FatFlat.Dev.L62
open FatFlat.Dev.Emb FatFlat.Hereditary

/-- inclusion `K_{a,b} ⊆ K_{a',b'}` -/
def biHom {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    completeBipartiteGraph (Fin a) (Fin b) →g completeBipartiteGraph (Fin a') (Fin b') where
  toFun := Sum.map (Fin.castLE ha) (Fin.castLE hb)
  map_rel' := by
    rintro (x | x) (y | y) h <;> simp_all [completeBipartiteGraph_adj]

lemma biHom_inj {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    Function.Injective (biHom ha hb) := by
  rintro (x | x) (y | y) h <;>
    simp_all [biHom]

theorem biclique_mono (r : ℕ) {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    Nonempty (subdividedBiclique r a b ↪g subdividedBiclique r a' b') :=
  ⟨sdEmb (biHom ha hb) (biHom_inj ha hb) (r - 1)⟩

theorem biweb_mono (r : ℕ) {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    Nonempty (biweb r a b ↪g biweb r a' b') :=
  ⟨webSdEmb (biHom ha hb) (biHom_inj ha hb) (r - 1)⟩

theorem mixweb_mono (r : ℕ) {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    Nonempty (mixweb r a b ↪g mixweb r a' b') := by
  have h := webSdEmbGen (biHom ha hb) (biHom_inj ha hb) (r - 1)
    (Set.range (Sum.inl : Fin a → Fin a ⊕ Fin b)) (Set.range (Sum.inl : Fin a' → Fin a' ⊕ Fin b'))
    (by
      intro u
      rcases u with u | u
      · simp [biHom]
      · simp [biHom])
  have e1 : (Sum.inl '' Set.range (Sum.inl : Fin a → Fin a ⊕ Fin b) :
      Set ((Fin a ⊕ Fin b) ⊕ Σ _ : (completeBipartiteGraph (Fin a) (Fin b)).edgeSet, Fin (r - 1 + 1))) = Set.range (fun i : Fin a => Sum.inl (Sum.inl i)) := by
    ext x; simp [Set.mem_range]
  have e2 : (Sum.inl '' Set.range (Sum.inl : Fin a' → Fin a' ⊕ Fin b') :
      Set ((Fin a' ⊕ Fin b') ⊕ Σ _ : (completeBipartiteGraph (Fin a') (Fin b')).edgeSet, Fin (r - 1 + 1))) = Set.range (fun i : Fin a' => Sum.inl (Sum.inl i)) := by
    ext x; simp [Set.mem_range]
  rw [e1, e2] at h
  exact ⟨h⟩

/-- transfer of shallow induced minors along a relabelling of the pattern -/
theorem shallow_transfer {W W' V : Type} (e : W ≃ W') (H : SimpleGraph W) (G : SimpleGraph V)
    (d : ℕ) (h : IsShallowInducedMinor (H.map e.toEmbedding) G d) :
    IsShallowInducedMinor H G d := by
  obtain ⟨M, hM⟩ := h
  refine ⟨{
    B := fun w => M.B (e w)
    nonempty := fun w => M.nonempty _
    disjoint := fun u w huw => M.disjoint (e.injective.ne huw)
    connected := fun w => M.connected _
    adj_iff := ?_ }, fun w => hM _⟩
  intro u w huw
  rw [M.adj_iff (e u) (e w) (e.injective.ne huw)]
  exact SimpleGraph.map_adj_apply

theorem relabel_fin {W : Type} [Finite W] (H : SimpleGraph W) :
    ∃ (n : ℕ) (H' : SimpleGraph (Fin n)), ∀ (V : Type) (G : SimpleGraph V) (d : ℕ),
      IsShallowInducedMinor H' G d → IsShallowInducedMinor H G d := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin W
  exact ⟨n, H.map e.toEmbedding, fun V G d h => shallow_transfer e H G d h⟩

end FatFlat.Dev.L62

namespace FatFlat.Hereditary
open FatFlat.Dev.L62

theorem chk_lemma_6_2 : ∃ R : ℕ → ℕ, ∀ d m : ℕ, ∃ (n : ℕ) (H : SimpleGraph (Fin n)),
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsShallowInducedMinor H G d →
      ∃ r : ℕ, 3 ≤ r ∧ r ≤ R d ∧
        (Nonempty (subdividedClique r m ↪g G) ∨ Nonempty (web r m ↪g G)) := by
  refine ⟨fun d => 16 * d + 7, fun d m => ?_⟩
  set m' := max m (m.choose 2) with hm'
  have h1 : m ≤ m' := le_max_left _ _
  have h2 : m.choose 2 ≤ m' := le_max_right _ _
  obtain ⟨M, hM⟩ := lemma_6_6 d m'
  obtain ⟨n, H', hH'⟩ := relabel_fin (subdividedBiclique 3 M M)
  refine ⟨n, H', fun V _ G hG => ?_⟩
  obtain ⟨r, hr3, hr8, h⟩ := hM V G (hH' V G d hG)
  obtain ⟨-, -, o3, o4, o5⟩ := observation_1 r m m hr3
  rcases h with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · obtain ⟨g⟩ := biclique_mono r h1 h2
    obtain ⟨c⟩ := o3
    exact ⟨2 * r + 1, by omega, by show 2 * r + 1 ≤ 16 * d + 7; omega, Or.inl ⟨(c.trans g).trans f⟩⟩
  · obtain ⟨g⟩ := biweb_mono r h1 h2
    obtain ⟨c⟩ := o4
    exact ⟨2 * r, by omega, by show 2 * r ≤ 16 * d + 7; omega, Or.inr ⟨(c.trans g).trans f⟩⟩
  · obtain ⟨g⟩ := mixweb_mono r h2 h1
    obtain ⟨c⟩ := o5
    exact ⟨2 * r, by omega, by show 2 * r ≤ 16 * d + 7; omega, Or.inl ⟨(c.trans g).trans f⟩⟩

end FatFlat.Hereditary
end

theorem solution : type_of% @FatFlat.Hereditary.chk_lemma_6_2 := @FatFlat.Hereditary.chk_lemma_6_2
