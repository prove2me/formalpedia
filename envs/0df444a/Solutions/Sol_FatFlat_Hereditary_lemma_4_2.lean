-- Prove2me | solution 1 for FatFlat.Hereditary.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:11:53.364441+00:00
-- url     : https://prove2.me/submissions/93731e31-c2af-4036-b023-0484ceea6ce3

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Classes
import Theorems.Thm_FatFlat_Hereditary_lemma_4_1

section
set_option autoImplicit false

namespace FatFlat.Dev.L42
open FatFlat.Hereditary

section Dist
variable {V : Type} {G : SimpleGraph V}

lemma hom_edist_le {V' : Type} {G' : SimpleGraph V'} (f : G →g G') (u v : V) :
    G'.edist (f u) (f v) ≤ G.edist u v := by
  by_cases h : G.edist u v = ⊤
  · simp [h]
  · obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top h
    calc G'.edist (f u) (f v) ≤ (p.map f).length := SimpleGraph.edist_le _
      _ = G.edist u v := by rw [SimpleGraph.Walk.length_map, hp]

lemma edist_le_induce (S : Set V) (a b : ↥S) :
    G.edist (a : V) (b : V) ≤ (G.induce S).edist a b :=
  hom_edist_le (SimpleGraph.Embedding.induce S).toHom a b

lemma enat_nat (x : ℕ∞) (n : ℕ) (h : x ≤ n) : ∃ k : ℕ, x = k ∧ k ≤ n :=
  ⟨x.toNat, (ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top n) h)).symm,
    by have := ENat.natCast_toNat (ne_top_of_le_ne_top (ENat.natCast_ne_top n) h)
       rw [← this] at h; exact_mod_cast h⟩

/-- Two vertex sets are *far* if distinct vertices... : disjoint and no edge between them. -/
def Far (G : SimpleGraph V) (S T : Set V) : Prop := ∀ x ∈ S, ∀ y ∈ T, 2 ≤ G.edist x y

lemma Far.symm {S T : Set V} (h : Far G S T) : Far G T S := fun x hx y hy => by
  rw [SimpleGraph.edist_comm]; exact h y hy x hx

lemma Far.union_left {S S' T : Set V} (h : Far G S T) (h' : Far G S' T) : Far G (S ∪ S') T := by
  rintro x (hx | hx) y hy
  · exact h x hx y hy
  · exact h' x hx y hy

lemma Far.union_right {S T T' : Set V} (h : Far G S T) (h' : Far G S T') : Far G S (T ∪ T') := by
  rintro x hx y (hy | hy)
  · exact h x hx y hy
  · exact h' x hx y hy

lemma Far.disjoint {S T : Set V} (h : Far G S T) : Disjoint S T := by
  rw [Set.disjoint_left]
  intro x hx hxT
  have := h x hx x hxT
  simp at this

lemma Far.not_adj {S T : Set V} (h : Far G S T) {x y : V} (hx : x ∈ S) (hy : y ∈ T) :
    ¬ G.Adj x y := by
  intro hadj
  have := h x hx y hy
  rw [SimpleGraph.edist_eq_one_iff_adj.mpr hadj] at this
  exact absurd this (by norm_num)

lemma far_of_balls {a b : V} {r s : ℕ} {S T : Set V} (hS : ∀ x ∈ S, G.edist x a ≤ r)
    (hT : ∀ y ∈ T, G.edist y b ≤ s) (hab : ((r + s + 2 : ℕ) : ℕ∞) ≤ G.edist a b) : Far G S T := by
  intro x hx y hy
  by_contra hc
  rw [not_le] at hc
  have h1 : G.edist x y ≤ 1 := by
    obtain ⟨k, hk, -⟩ := enat_nat _ 2 hc.le
    rw [hk] at hc ⊢
    have : k < 2 := by exact_mod_cast hc
    exact_mod_cast (by omega : k ≤ 1)
  have h2 : G.edist a b ≤ G.edist a x + (G.edist x y + G.edist y b) :=
    (SimpleGraph.edist_triangle (v := x)).trans
      (add_le_add_right SimpleGraph.edist_triangle _)
  have ha : G.edist a x ≤ r := by rw [SimpleGraph.edist_comm]; exact hS x hx
  have hb : G.edist y b ≤ s := hT y hy
  have h3 : G.edist a b ≤ ((r + (1 + s) : ℕ) : ℕ∞) := by
    refine h2.trans ?_
    push_cast
    gcongr
  have h4 := hab.trans h3
  have h5 : r + s + 2 ≤ r + (1 + s) := by exact_mod_cast h4
  omega

end Dist

section Radius
variable {V : Type} {G : SimpleGraph V}

lemma radius_mono {S : Set V} {r r' : ℕ} (h : RadiusLE G S r) (hr : r ≤ r') : RadiusLE G S r' := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun v => (hc v).trans (by exact_mod_cast hr)⟩

lemma radius_nonempty {S : Set V} {r : ℕ} (h : RadiusLE G S r) : S.Nonempty := by
  obtain ⟨c, -⟩ := h
  exact ⟨c, c.2⟩

lemma radius_connected {S : Set V} {r : ℕ} (h : RadiusLE G S r) : (G.induce S).Connected := by
  obtain ⟨c, hc⟩ := h
  have hr : ∀ v, (G.induce S).Reachable c v := fun v =>
    SimpleGraph.reachable_of_edist_ne_top
      (ne_top_of_le_ne_top (ENat.natCast_ne_top r) (hc v))
  have : Nonempty ↥S := ⟨c⟩
  exact ⟨fun u v => (hr u).symm.trans (hr v)⟩

lemma radius_image {V' : Type} {G' : SimpleGraph V'} (F : G' ↪g G) {S : Set V'} {r : ℕ}
    (h : RadiusLE G' S r) : RadiusLE G (F '' S) r := by
  obtain ⟨c, hc⟩ := h
  let φ : G'.induce S →g G.induce (F '' S) :=
    ⟨fun x => ⟨F x, ⟨x, x.2, rfl⟩⟩, by
      intro x y hxy
      simpa using F.map_adj_iff.mpr hxy⟩
  refine ⟨φ c, fun v' => ?_⟩
  obtain ⟨y, hy, hyv⟩ := v'.2
  have : v' = φ ⟨y, hy⟩ := Subtype.ext hyv.symm
  rw [this]
  exact (hom_edist_le φ c ⟨y, hy⟩).trans (hc _)

end Radius

section OneSub
variable {W : Type}

lemma oneSub_adj_inl_inr (H : SimpleGraph W) (u : W) (e : H.edgeSet) (i : Fin (0 + 1)) :
    (oneSubdivision H).Adj (Sum.inl u) (Sum.inr ⟨e, i⟩) ↔ u ∈ (e : Sym2 W) := by
  unfold oneSubdivision SparseDisc.subdivide
  simp only [SimpleGraph.fromRel_adj]
  have himg : s(((Quot.out (e : Sym2 W)).1), ((Quot.out (e : Sym2 W)).2)) = (e : Sym2 W) :=
    Quot.out_eq _
  have hi : i.val = 0 := by omega
  constructor
  · rintro ⟨-, h | h⟩
    · simp only [hi, and_true] at h
      rcases h with h | h
      · rw [← himg]; simp [h]
      · rw [← himg]; simp [h]
    · simp at h
  · intro hu
    rw [← himg] at hu
    have hne : (Sum.inl u : W ⊕ Σ _ : H.edgeSet, Fin (0 + 1)) ≠ Sum.inr ⟨e, i⟩ := by simp
    refine ⟨hne, Or.inl ?_⟩
    simp only [hi, and_true]
    rcases Sym2.mem_iff.mp hu with h | h
    · exact Or.inl h
    · exact Or.inr h

lemma oneSub_not_adj_inl_inl (H : SimpleGraph W) (u u' : W) :
    ¬ (oneSubdivision H).Adj (Sum.inl u) (Sum.inl u') := by
  unfold oneSubdivision SparseDisc.subdivide
  simp [SimpleGraph.fromRel_adj]

lemma oneSub_not_adj_inr_inr (H : SimpleGraph W) (x x' : Σ _ : H.edgeSet, Fin (0 + 1)) :
    ¬ (oneSubdivision H).Adj (Sum.inr x) (Sum.inr x') := by
  obtain ⟨e, i⟩ := x
  obtain ⟨e', j⟩ := x'
  unfold oneSubdivision SparseDisc.subdivide
  simp only [SimpleGraph.fromRel_adj]
  have hi : i.val = 0 := by omega
  have hj : j.val = 0 := by omega
  rintro ⟨-, h | h⟩ <;> omega

end OneSub

section Model
variable {W V : Type}

lemma mkModel (H : SimpleGraph W) (G : SimpleGraph V) (a b : ℕ) (P : W → Set V)
    (Q : H.edgeSet → Set V)
    (hPr : ∀ u, RadiusLE G (P u) a) (hQr : ∀ e, RadiusLE G (Q e) b)
    (hPP : ∀ u u', u ≠ u' → Far G (P u) (P u'))
    (hQQ : ∀ e e', e ≠ e' → Far G (Q e) (Q e'))
    (hfar : ∀ u (e : H.edgeSet), u ∉ (e : Sym2 W) → Far G (P u) (Q e))
    (hadj : ∀ u (e : H.edgeSet), u ∈ (e : Sym2 W) →
      Disjoint (P u) (Q e) ∧ ∃ x ∈ P u, ∃ y ∈ Q e, G.Adj x y) :
    IsShallowInducedMinorOneSubdiv H G a b := by
  let B : W ⊕ (Σ _ : H.edgeSet, Fin (0 + 1)) → Set V := Sum.elim P (fun s => Q s.1)
  have hBr : ∀ w, ∃ r, RadiusLE G (B w) r := by
    rintro (u | s)
    · exact ⟨a, hPr u⟩
    · exact ⟨b, hQr s.1⟩
  have hsig : ∀ s s' : (Σ _ : H.edgeSet, Fin (0 + 1)), s ≠ s' → s.1 ≠ s'.1 := by
    rintro ⟨e, i⟩ ⟨e', j⟩ hne h
    simp only at h
    subst h
    have h1 := i.2
    have h2 := j.2
    have : i = j := Fin.ext (by omega)
    exact hne (by rw [this])
  refine ⟨⟨B, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro (u | s)
    · exact radius_nonempty (hPr u)
    · exact radius_nonempty (hQr s.1)
  · rintro (u | s) (u' | s') hne
    · exact (hPP u u' (fun h => hne (by rw [h]))).disjoint
    · by_cases hu : u ∈ (s'.1 : Sym2 W)
      · exact (hadj u s'.1 hu).1
      · exact (hfar u s'.1 hu).disjoint
    · by_cases hu : u' ∈ (s.1 : Sym2 W)
      · exact (hadj u' s.1 hu).1.symm
      · exact (hfar u' s.1 hu).disjoint.symm
    · exact (hQQ s.1 s'.1 (hsig s s' (fun h => hne (by rw [h])))).disjoint
  · intro w
    obtain ⟨r, hr⟩ := hBr w
    exact radius_connected hr
  · rintro (u | s) (u' | s') hne
    · constructor
      · rintro ⟨x, hx, y, hy, hxy⟩
        exact absurd hxy ((hPP u u' (fun h => hne (by rw [h]))).not_adj hx hy)
      · intro h; exact absurd h (oneSub_not_adj_inl_inl H u u')
    · by_cases hu : u ∈ (s'.1 : Sym2 W)
      · refine ⟨fun _ => ?_, fun _ => (hadj u s'.1 hu).2⟩
        exact (oneSub_adj_inl_inr H u s'.1 s'.2).mpr hu
      · constructor
        · rintro ⟨x, hx, y, hy, hxy⟩
          exact absurd hxy ((hfar u s'.1 hu).not_adj hx hy)
        · intro h
          exact absurd ((oneSub_adj_inl_inr H u s'.1 s'.2).mp h) hu
    · by_cases hu : u' ∈ (s.1 : Sym2 W)
      · refine ⟨fun _ => ?_, fun _ => ?_⟩
        · exact ((oneSub_adj_inl_inr H u' s.1 s.2).mpr hu).symm
        · obtain ⟨x, hx, y, hy, hxy⟩ := (hadj u' s.1 hu).2
          exact ⟨y, hy, x, hx, hxy.symm⟩
      · constructor
        · rintro ⟨y, hy, x, hx, hxy⟩
          exact absurd hxy.symm ((hfar u' s.1 hu).not_adj hx hy)
        · intro h
          exact absurd ((oneSub_adj_inl_inr H u' s.1 s.2).mp h.symm) hu
    · constructor
      · rintro ⟨x, hx, y, hy, hxy⟩
        exact absurd hxy ((hQQ s.1 s'.1 (hsig s s' (fun h => hne (by rw [h])))).not_adj hx hy)
      · intro h; exact absurd h (oneSub_not_adj_inr_inr H s s')
  · exact fun u => hPr u
  · exact fun s => hQr s.1

lemma transfer {V' : Type} (H : SimpleGraph W) {G' : SimpleGraph V'} {G : SimpleGraph V}
    (F : G' ↪g G) (a b : ℕ) (h : IsShallowInducedMinorOneSubdiv H G' a b) :
    IsShallowInducedMinorOneSubdiv H G a b := by
  obtain ⟨M, hA, hB⟩ := h
  have hR : ∀ w, ∃ r, RadiusLE G' (M.B w) r := by
    rintro (u | x)
    · exact ⟨a, hA u⟩
    · exact ⟨b, hB x⟩
  refine ⟨⟨fun w => F '' (M.B w), fun w => (M.nonempty w).image F, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro u w huw
    exact (Set.disjoint_image_iff F.injective).mpr (M.disjoint huw)
  · intro w
    obtain ⟨r, hr⟩ := hR w
    exact radius_connected (radius_image F hr)
  · intro u w huw
    rw [← M.adj_iff u w huw]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hadj⟩
      exact ⟨x, hx, y, hy, F.map_adj_iff.mp hadj⟩
    · rintro ⟨x, hx, y, hy, hadj⟩
      exact ⟨F x, ⟨x, hx, rfl⟩, F y, ⟨y, hy, rfl⟩, F.map_adj_iff.mpr hadj⟩
  · exact fun u => radius_image F (hA u)
  · exact fun x => radius_image F (hB x)

lemma mono_radius (H : SimpleGraph W) (G : SimpleGraph V) {a a' b b' : ℕ}
    (h : IsShallowInducedMinorOneSubdiv H G a b) (ha : a ≤ a') (hb : b ≤ b') :
    IsShallowInducedMinorOneSubdiv H G a' b' := by
  obtain ⟨M, hA, hB⟩ := h
  exact ⟨M, fun u => radius_mono (hA u) ha, fun x => radius_mono (hB x) hb⟩

end Model

section Path
variable {V : Type} {G : SimpleGraph V}

lemma path_edist (S : Set V) (p : ℕ → V) (a : ℕ) :
    ∀ n : ℕ, ∀ (hS : ∀ u, a ≤ u → u ≤ a + n → p u ∈ S),
      (∀ u, a ≤ u → u < a + n → G.Adj (p u) (p (u + 1))) →
      (G.induce S).edist ⟨p a, hS a le_rfl (by omega)⟩ ⟨p (a + n), hS (a + n) (by omega) le_rfl⟩
        ≤ n := by
  intro n
  induction n with
  | zero =>
    intro hS _
    simp
  | succ n ih =>
    intro hS hadj
    have hS' : ∀ u, a ≤ u → u ≤ a + n → p u ∈ S := fun u h1 h2 => hS u h1 (by omega)
    have h1 := ih hS' (fun u h1 h2 => hadj u h1 (by omega))
    have h2 : (G.induce S).edist ⟨p (a + n), hS' (a + n) (by omega) le_rfl⟩
        ⟨p (a + (n + 1)), hS (a + (n + 1)) (by omega) le_rfl⟩ = 1 := by
      rw [SimpleGraph.edist_eq_one_iff_adj]
      have := hadj (a + n) (by omega) (by omega)
      exact this
    calc _ ≤ _ := SimpleGraph.edist_triangle (v := ⟨p (a + n), hS' (a + n) (by omega) le_rfl⟩)
      _ ≤ (n : ℕ∞) + 1 := add_le_add h1 h2.le
      _ = ((n + 1 : ℕ) : ℕ∞) := by push_cast; rfl

lemma path_edist_G (p : ℕ → V) (a n : ℕ)
    (hadj : ∀ u, a ≤ u → u < a + n → G.Adj (p u) (p (u + 1))) :
    G.edist (p a) (p (a + n)) ≤ n :=
  (edist_le_induce (G := G) Set.univ ⟨p a, trivial⟩ ⟨p (a + n), trivial⟩).trans
    (path_edist Set.univ p a n (fun _ _ _ => trivial) hadj)

lemma geo_path (x y : V) (L : ℕ) (h : G.edist x y = L) :
    ∃ p : ℕ → V, p 0 = x ∧ p L = y ∧ ∀ t, t < L → G.Adj (p t) (p (t + 1)) := by
  obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_eq_coe h
  refine ⟨w.getVert, w.getVert_zero, ?_, fun t ht => w.adj_getVert_succ (hw ▸ ht)⟩
  rw [← hw]
  exact w.getVert_length

/-- Along a geodesic, the distances from the end points are exact. -/
lemma geo_exact (p : ℕ → V) (L : ℕ) (h : G.edist (p 0) (p L) = L)
    (hadj : ∀ t, t < L → G.Adj (p t) (p (t + 1))) (t : ℕ) (ht : t ≤ L) :
    G.edist (p 0) (p t) = t ∧ G.edist (p t) (p L) = ((L - t : ℕ) : ℕ∞) := by
  have h1 : G.edist (p 0) (p t) ≤ t := by
    have := path_edist_G (G := G) p 0 t (fun u _ hu => hadj u (by omega))
    simpa using this
  have h2 : G.edist (p t) (p L) ≤ ((L - t : ℕ) : ℕ∞) := by
    have := path_edist_G (G := G) p t (L - t) (fun u _ hu => hadj u (by omega))
    have e : t + (L - t) = L := by omega
    rw [e] at this
    exact this
  obtain ⟨k1, hk1, hk1'⟩ := enat_nat _ t h1
  obtain ⟨k2, hk2, hk2'⟩ := enat_nat _ (L - t) h2
  have h3 : G.edist (p 0) (p L) ≤ G.edist (p 0) (p t) + G.edist (p t) (p L) :=
    SimpleGraph.edist_triangle
  rw [h, hk1, hk2] at h3
  have h4 : L ≤ k1 + k2 := by exact_mod_cast h3
  rw [hk1, hk2]
  constructor
  · congr 1; omega
  · congr 1; omega

end Path

end FatFlat.Dev.L42
end

section
set_option autoImplicit false

namespace FatFlat.Dev.L42
open FatFlat.Hereditary

section Geo
variable {V : Type}

/-- Data for the final stage of Lemma 4.2: vertices `x i` (a `2d`-scattered family) and `v j`
(a `37`-scattered family) with `d + 6 ≥ dist(x i, v j) ≥ d - 5`, and geodesics `p i j`
from `x i` to `v j`; here `d = e + 32`. -/
structure Geo (G : SimpleGraph V) (h e : ℕ) where
  x : Fin h → V
  v : Fin h → V
  L : Fin h → Fin h → ℕ
  p : Fin h → Fin h → ℕ → V
  hxx : ∀ i k, i ≠ k → ((2 * (e + 32) : ℕ) : ℕ∞) < G.edist (x i) (x k)
  hvv : ∀ i k, i ≠ k → ((37 : ℕ) : ℕ∞) < G.edist (v i) (v k)
  hL : ∀ i j, G.edist (x i) (v j) = L i j
  hL1 : ∀ i j, e + 27 ≤ L i j
  hL2 : ∀ i j, L i j ≤ e + 38
  hp0 : ∀ i j, p i j 0 = x i
  hpL : ∀ i j, p i j (L i j) = v j
  hpa : ∀ i j t, t < L i j → G.Adj (p i j t) (p i j (t + 1))

variable {G : SimpleGraph V} {h e : ℕ} (D : Geo G h e)

/-- the middle part of the geodesic from `x i` to `v j` -/
def Geo.Mid (i j : Fin h) : Set V :=
  {y | ∃ t, e + 20 ≤ t ∧ t + 7 ≤ D.L i j ∧ y = D.p i j t}

def Geo.Bx (i : Fin h) : Set V := {y | G.edist y (D.x i) ≤ ((e + 19 : ℕ) : ℕ∞)}
def Geo.Bv (j : Fin h) : Set V := {y | G.edist y (D.v j) ≤ ((6 : ℕ) : ℕ∞)}
def Geo.P (i : Fin h) : Set V := (D.Bx i ∪ D.Mid i i) ∪ D.Bv i

lemma Geo.exact (i j : Fin h) (t : ℕ) (ht : t ≤ D.L i j) :
    G.edist (D.x i) (D.p i j t) = t ∧ G.edist (D.p i j t) (D.v j) = ((D.L i j - t : ℕ) : ℕ∞) := by
  have := geo_exact (G := G) (D.p i j) (D.L i j)
    (by rw [D.hp0, D.hpL]; exact D.hL i j) (D.hpa i j) t ht
  rw [D.hp0, D.hpL] at this
  exact this

lemma Geo.mid_x {i j : Fin h} {y : V} (hy : y ∈ D.Mid i j) :
    G.edist y (D.x i) ≤ ((e + 31 : ℕ) : ℕ∞) := by
  obtain ⟨t, h1, h2, rfl⟩ := hy
  have := (D.exact i j t (by omega)).1
  rw [SimpleGraph.edist_comm, this]
  have := D.hL2 i j
  exact_mod_cast (by omega : t ≤ e + 31)

lemma Geo.mid_v {i j : Fin h} {y : V} (hy : y ∈ D.Mid i j) :
    G.edist y (D.v j) ≤ ((18 : ℕ) : ℕ∞) := by
  obtain ⟨t, h1, h2, rfl⟩ := hy
  have := (D.exact i j t (by omega)).2
  rw [this]
  have := D.hL2 i j
  exact_mod_cast (by omega : D.L i j - t ≤ 18)

lemma Geo.mid_nbx {i j : Fin h} {y : V} (hy : y ∈ D.Mid i j) : y ∉ D.Bx i := by
  obtain ⟨t, h1, h2, rfl⟩ := hy
  intro hb
  have := (D.exact i j t (by omega)).1
  unfold Geo.Bx at hb
  simp only [Set.mem_ofPred_eq] at hb
  rw [SimpleGraph.edist_comm, this] at hb
  have : t ≤ e + 19 := by exact_mod_cast hb
  omega

lemma Geo.mid_nbv {i j : Fin h} {y : V} (hy : y ∈ D.Mid i j) : y ∉ D.Bv j := by
  obtain ⟨t, h1, h2, rfl⟩ := hy
  intro hb
  have := (D.exact i j t (by omega)).2
  unfold Geo.Bv at hb
  simp only [Set.mem_ofPred_eq] at hb
  rw [this] at hb
  have : D.L i j - t ≤ 6 := by exact_mod_cast hb
  omega

lemma Geo.far_xx {i k : Fin h} (hik : i ≠ k) {S T : Set V}
    (hS : ∀ y ∈ S, G.edist y (D.x i) ≤ ((e + 31 : ℕ) : ℕ∞))
    (hT : ∀ y ∈ T, G.edist y (D.x k) ≤ ((e + 31 : ℕ) : ℕ∞)) : Far G S T := by
  refine far_of_balls hS hT ?_
  have h1 := (D.hxx i k hik).le
  have : e + 31 + (e + 31) + 2 = 2 * (e + 32) := by omega
  rw [this]; exact h1

lemma Geo.far_vv {j l : Fin h} (hjl : j ≠ l) {S T : Set V}
    (hS : ∀ y ∈ S, G.edist y (D.v j) ≤ ((18 : ℕ) : ℕ∞))
    (hT : ∀ y ∈ T, G.edist y (D.v l) ≤ ((18 : ℕ) : ℕ∞)) : Far G S T := by
  refine far_of_balls hS hT ?_
  have h1 : ((37 : ℕ) : ℕ∞) + 1 ≤ G.edist (D.v j) (D.v l) := Order.add_one_le_of_lt (D.hvv j l hjl)
  have : (((18 + 18 + 2 : ℕ)) : ℕ∞) = ((37 : ℕ) : ℕ∞) + 1 := by norm_num
  rw [this]; exact h1

lemma Geo.far_bxbv (i j : Fin h) : Far G (D.Bx i) (D.Bv j) := by
  refine far_of_balls (fun y hy => hy) (fun y hy => hy) ?_
  rw [D.hL i j]
  have := D.hL1 i j
  exact_mod_cast (by omega : e + 19 + 6 + 2 ≤ D.L i j)

lemma Geo.bx_x {i : Fin h} {y : V} (hy : y ∈ D.Bx i) : G.edist y (D.x i) ≤ ((e + 31 : ℕ) : ℕ∞) :=
  hy.trans (by exact_mod_cast (by omega : e + 19 ≤ e + 31))

lemma Geo.bv_v {j : Fin h} {y : V} (hy : y ∈ D.Bv j) : G.edist y (D.v j) ≤ ((18 : ℕ) : ℕ∞) :=
  hy.trans (by exact_mod_cast (by omega : 6 ≤ 18))

lemma Geo.far_PP {u u' : Fin h} (huu : u ≠ u') : Far G (D.P u) (D.P u') := by
  unfold Geo.P
  refine Far.union_left (Far.union_left ?_ ?_) ?_ <;>
    refine Far.union_right (Far.union_right ?_ ?_) ?_
  · exact D.far_xx huu (fun y hy => D.bx_x hy) (fun y hy => D.bx_x hy)
  · exact D.far_xx huu (fun y hy => D.bx_x hy) (fun y hy => D.mid_x hy)
  · exact D.far_bxbv u u'
  · exact D.far_xx huu (fun y hy => D.mid_x hy) (fun y hy => D.bx_x hy)
  · exact D.far_xx huu (fun y hy => D.mid_x hy) (fun y hy => D.mid_x hy)
  · exact D.far_vv huu (fun y hy => D.mid_v hy) (fun y hy => D.bv_v hy)
  · exact (D.far_bxbv u' u).symm
  · exact D.far_vv huu (fun y hy => D.bv_v hy) (fun y hy => D.mid_v hy)
  · exact D.far_vv huu (fun y hy => D.bv_v hy) (fun y hy => D.bv_v hy)

lemma Geo.far_QQ {i j k l : Fin h} (hne : ¬ (i = k ∧ j = l)) :
    Far G (D.Mid i j) (D.Mid k l) := by
  by_cases hik : i = k
  · have hjl : j ≠ l := fun hjl => hne ⟨hik, hjl⟩
    exact D.far_vv hjl (fun y hy => D.mid_v hy) (fun y hy => D.mid_v hy)
  · exact D.far_xx hik (fun y hy => D.mid_x hy) (fun y hy => D.mid_x hy)

lemma Geo.far_PQ {u i j : Fin h} (hui : u ≠ i) (huj : u ≠ j) : Far G (D.P u) (D.Mid i j) := by
  unfold Geo.P
  refine Far.union_left (Far.union_left ?_ ?_) ?_
  · exact D.far_xx hui (fun y hy => D.bx_x hy) (fun y hy => D.mid_x hy)
  · exact D.far_xx hui (fun y hy => D.mid_x hy) (fun y hy => D.mid_x hy)
  · exact D.far_vv huj (fun y hy => D.bv_v hy) (fun y hy => D.mid_v hy)

lemma Geo.disj_i {i j : Fin h} (hij : i ≠ j) : Disjoint (D.P i) (D.Mid i j) := by
  unfold Geo.P
  refine Disjoint.union_left (Disjoint.union_left ?_ ?_) ?_
  · rw [Set.disjoint_left]
    intro y hy hy'
    exact D.mid_nbx hy' hy
  · exact (D.far_vv hij (fun y hy => D.mid_v hy) (fun y hy => D.mid_v hy)).disjoint
  · exact (D.far_vv hij (fun y hy => D.bv_v hy) (fun y hy => D.mid_v hy)).disjoint

lemma Geo.disj_j {i j : Fin h} (hij : i ≠ j) : Disjoint (D.P j) (D.Mid i j) := by
  unfold Geo.P
  refine Disjoint.union_left (Disjoint.union_left ?_ ?_) ?_
  · exact (D.far_xx hij.symm (fun y hy => D.bx_x hy) (fun y hy => D.mid_x hy)).disjoint
  · exact (D.far_xx hij.symm (fun y hy => D.mid_x hy) (fun y hy => D.mid_x hy)).disjoint
  · rw [Set.disjoint_left]
    intro y hy hy'
    exact D.mid_nbv hy' hy

lemma Geo.mid_mem (i j : Fin h) (t : ℕ) (h1 : e + 20 ≤ t) (h2 : t + 7 ≤ D.L i j) :
    D.p i j t ∈ D.Mid i j := ⟨t, h1, h2, rfl⟩

lemma Geo.adj_i (i j : Fin h) : ∃ y ∈ D.P i, ∃ z ∈ D.Mid i j, G.Adj y z := by
  have hL1 := D.hL1 i j
  refine ⟨D.p i j (e + 19), ?_, D.p i j (e + 20), D.mid_mem i j _ le_rfl (by omega), ?_⟩
  · left; left
    have := (D.exact i j (e + 19) (by omega)).1
    show G.edist _ _ ≤ _
    rw [SimpleGraph.edist_comm, this]
  · exact D.hpa i j (e + 19) (by omega)

lemma Geo.adj_j (i j : Fin h) : ∃ y ∈ D.P j, ∃ z ∈ D.Mid i j, G.Adj y z := by
  have hL1 := D.hL1 i j
  refine ⟨D.p i j (D.L i j - 6), ?_, D.p i j (D.L i j - 7),
    D.mid_mem i j _ (by omega) (by omega), ?_⟩
  · right
    have := (D.exact i j (D.L i j - 6) (by omega)).2
    show G.edist _ _ ≤ _
    rw [this]
    exact_mod_cast (by omega : D.L i j - (D.L i j - 6) ≤ 6)
  · have := D.hpa i j (D.L i j - 7) (by omega)
    have e1 : D.L i j - 7 + 1 = D.L i j - 6 := by omega
    rw [e1] at this
    exact this.symm

end Geo

section Radius2
variable {V : Type} {G : SimpleGraph V}

lemma path_edist_pts (S : Set V) (p : ℕ → V) (a n : ℕ) (hS : ∀ u, a ≤ u → u ≤ a + n → p u ∈ S)
    (hadj : ∀ u, a ≤ u → u < a + n → G.Adj (p u) (p (u + 1))) (u w : ↥S) (hu : (u : V) = p a)
    (hw : (w : V) = p (a + n)) : (G.induce S).edist u w ≤ n := by
  have := path_edist S p a n hS hadj
  have e1 : u = ⟨p a, hS a le_rfl (by omega)⟩ := Subtype.ext hu
  have e2 : w = ⟨p (a + n), hS (a + n) (by omega) le_rfl⟩ := Subtype.ext hw
  rw [e1, e2]; exact this

lemma ball_ind (S : Set V) (z : V) (r : ℕ) (hS : ∀ y, G.edist y z ≤ r → y ∈ S) (y : V)
    (hy : G.edist y z ≤ r) (hz : z ∈ S) :
    (G.induce S).edist ⟨z, hz⟩ ⟨y, hS y hy⟩ ≤ r := by
  have hy' : G.edist z y ≤ r := by rw [SimpleGraph.edist_comm]; exact hy
  obtain ⟨k, hk, hkr⟩ := enat_nat _ r hy'
  obtain ⟨p, hp0, hpk, hpa⟩ := geo_path z y k hk
  have hmem : ∀ u, 0 ≤ u → u ≤ 0 + k → p u ∈ S := by
    intro u _ hu
    apply hS
    have := path_edist_G (G := G) p 0 u (fun t _ ht => hpa t (by omega))
    simp only [zero_add, hp0] at this
    rw [SimpleGraph.edist_comm]
    refine this.trans ?_
    exact_mod_cast (by omega : u ≤ r)
  have := path_edist_pts (G := G) S p 0 k hmem (fun t _ ht => hpa t (by omega)) ⟨z, hz⟩
    ⟨y, hS y hy⟩ (by simpa using hp0.symm) (by simpa using hpk.symm)
  exact this.trans (by exact_mod_cast hkr)

variable {h e : ℕ} (D : Geo G h e)

lemma Geo.p_mem_P (i : Fin h) (u : ℕ) (hu : u ≤ D.L i i) : D.p i i u ∈ D.P i := by
  have hL2 := D.hL2 i i
  by_cases h1 : u ≤ e + 19
  · left; left
    have := (D.exact i i u hu).1
    show G.edist _ _ ≤ _
    rw [SimpleGraph.edist_comm, this]
    exact_mod_cast h1
  · by_cases h2 : D.L i i ≤ u + 6
    · right
      have := (D.exact i i u hu).2
      show G.edist _ _ ≤ _
      rw [this]
      exact_mod_cast (by omega : D.L i i - u ≤ 6)
    · left; right
      exact ⟨u, by omega, by omega, rfl⟩

lemma Geo.P_radius (i : Fin h) : RadiusLE G (D.P i) (e + 44) := by
  have hxP : D.x i ∈ D.P i := by
    left; left
    show G.edist _ _ ≤ _
    simp
  have hvP : D.v i ∈ D.P i := by
    right
    show G.edist _ _ ≤ _
    simp
  have hL1 := D.hL1 i i
  have hL2 := D.hL2 i i
  refine ⟨⟨D.x i, hxP⟩, ?_⟩
  rintro ⟨y, hy⟩
  rcases hy with (hy | hy) | hy
  · have := ball_ind (G := G) (D.P i) (D.x i) (e + 19)
      (fun y' hy' => Or.inl (Or.inl hy')) y hy hxP
    exact this.trans (by exact_mod_cast (by omega : e + 19 ≤ e + 44))
  · obtain ⟨t, h1, h2, rfl⟩ := hy
    have := path_edist_pts (G := G) (D.P i) (D.p i i) 0 t
      (fun u _ hu => D.p_mem_P i u (by omega))
      (fun u _ hu => D.hpa i i u (by omega)) ⟨D.x i, hxP⟩ ⟨D.p i i t, D.p_mem_P i t (by omega)⟩
      (by simpa using (D.hp0 i i).symm) (by simp)
    exact this.trans (by exact_mod_cast (by omega : t ≤ e + 44))
  · have h1 : (G.induce (D.P i)).edist ⟨D.x i, hxP⟩ ⟨D.v i, hvP⟩ ≤ D.L i i := by
      have := path_edist_pts (G := G) (D.P i) (D.p i i) 0 (D.L i i)
        (fun u _ hu => D.p_mem_P i u (by omega))
        (fun u _ hu => D.hpa i i u (by omega)) ⟨D.x i, hxP⟩ ⟨D.v i, hvP⟩
        (by simpa using (D.hp0 i i).symm) (by simpa using (D.hpL i i).symm)
      exact this
    have h2 := ball_ind (G := G) (D.P i) (D.v i) 6 (fun y' hy' => Or.inr hy') y hy hvP
    calc _ ≤ _ := SimpleGraph.edist_triangle (v := ⟨D.v i, hvP⟩)
      _ ≤ ((D.L i i : ℕ) : ℕ∞) + ((6 : ℕ) : ℕ∞) := add_le_add h1 h2
      _ ≤ _ := by exact_mod_cast (by omega : D.L i i + 6 ≤ e + 44)

lemma Geo.Mid_radius (i j : Fin h) : RadiusLE G (D.Mid i j) 6 := by
  have hL1 := D.hL1 i j
  have hL2 := D.hL2 i j
  set tc : ℕ := e + 20 + (D.L i j - 7 - (e + 20)) / 2 with htc
  have hcm : D.p i j tc ∈ D.Mid i j := D.mid_mem i j _ (by omega) (by omega)
  refine ⟨⟨D.p i j tc, hcm⟩, ?_⟩
  rintro ⟨y, hy⟩
  obtain ⟨t, h1, h2, rfl⟩ := hy
  have hm : ∀ u, e + 20 ≤ u → u + 7 ≤ D.L i j → D.p i j u ∈ D.Mid i j :=
    fun u a b => D.mid_mem i j u a b
  by_cases hle : tc ≤ t
  · have := path_edist_pts (G := G) (D.Mid i j) (D.p i j) tc (t - tc)
      (fun u hu1 hu2 => hm u (by omega) (by omega))
      (fun u hu1 hu2 => D.hpa i j u (by omega)) ⟨D.p i j tc, hcm⟩ ⟨D.p i j t, hm t h1 h2⟩
      rfl (by simp only; congr 1; omega)
    exact this.trans (by exact_mod_cast (by omega : t - tc ≤ 6))
  · have := path_edist_pts (G := G) (D.Mid i j) (D.p i j) t (tc - t)
      (fun u hu1 hu2 => hm u (by omega) (by omega))
      (fun u hu1 hu2 => D.hpa i j u (by omega)) ⟨D.p i j t, hm t h1 h2⟩ ⟨D.p i j tc, hcm⟩
      rfl (by simp only; congr 1; omega)
    rw [SimpleGraph.edist_comm]
    exact this.trans (by exact_mod_cast (by omega : tc - t ≤ 6))

end Radius2

section Assemble
variable {V : Type} {G : SimpleGraph V} {h e : ℕ} (D : Geo G h e)

lemma edge_ne (ε : (⊤ : SimpleGraph (Fin h)).edgeSet) :
    (Quot.out (ε : Sym2 (Fin h))).1 ≠ (Quot.out (ε : Sym2 (Fin h))).2 := by
  have h1 : s((Quot.out (ε : Sym2 (Fin h))).1, (Quot.out (ε : Sym2 (Fin h))).2) =
      (ε : Sym2 (Fin h)) := Quot.out_eq _
  have h2 := ε.2
  rw [← h1] at h2
  simpa using h2

lemma edge_ext (ε ε' : (⊤ : SimpleGraph (Fin h)).edgeSet)
    (h1 : (Quot.out (ε : Sym2 (Fin h))).1 = (Quot.out (ε' : Sym2 (Fin h))).1)
    (h2 : (Quot.out (ε : Sym2 (Fin h))).2 = (Quot.out (ε' : Sym2 (Fin h))).2) : ε = ε' := by
  apply Subtype.ext
  rw [← Quot.out_eq (ε : Sym2 (Fin h)), ← Quot.out_eq (ε' : Sym2 (Fin h))]
  have e1 : (Quot.out (ε : Sym2 (Fin h))) = (Quot.out (ε' : Sym2 (Fin h))) :=
    Prod.ext h1 h2
  rw [e1]

lemma edge_mem (ε : (⊤ : SimpleGraph (Fin h)).edgeSet) (u : Fin h) :
    u ∈ (ε : Sym2 (Fin h)) ↔
      u = (Quot.out (ε : Sym2 (Fin h))).1 ∨ u = (Quot.out (ε : Sym2 (Fin h))).2 := by
  have h1 : s((Quot.out (ε : Sym2 (Fin h))).1, (Quot.out (ε : Sym2 (Fin h))).2) =
      (ε : Sym2 (Fin h)) := Quot.out_eq _
  conv_lhs => rw [← h1]
  simp [Sym2.mem_iff]

theorem model_of_geo (D : Geo G h e) :
    IsShallowInducedMinorOneSubdiv (⊤ : SimpleGraph (Fin h)) G (3 * (e + 32)) 6 := by
  refine mkModel (⊤ : SimpleGraph (Fin h)) G (3 * (e + 32)) 6 D.P
    (fun ε => D.Mid (Quot.out (ε : Sym2 (Fin h))).1 (Quot.out (ε : Sym2 (Fin h))).2)
    (fun u => radius_mono (D.P_radius u) (by omega)) (fun ε => D.Mid_radius _ _)
    (fun u u' huu => D.far_PP huu) ?_ ?_ ?_
  · intro ε ε' hne
    refine D.far_QQ ?_
    rintro ⟨h1, h2⟩
    exact hne (edge_ext ε ε' h1 h2)
  · intro u ε hu
    rw [edge_mem] at hu
    exact D.far_PQ (fun h => hu (Or.inl h)) (fun h => hu (Or.inr h))
  · intro u ε hu
    have hne := edge_ne ε
    rw [edge_mem] at hu
    rcases hu with rfl | rfl
    · exact ⟨D.disj_i hne, D.adj_i _ _⟩
    · exact ⟨D.disj_j hne, D.adj_j _ _⟩

end Assemble

end FatFlat.Dev.L42
end

section
set_option autoImplicit false

namespace FatFlat.Dev.L42
open FatFlat.Hereditary

lemma nat_of_rpow (c y : ℕ) (h : (c : ℝ) ^ ((1 : ℝ) / 10) ≤ y) : c ≤ y ^ 10 := by
  have : (c : ℝ) ≤ (y : ℝ) ^ 10 := by
    calc (c : ℝ) = ((c : ℝ) ^ ((1 : ℝ) / 10)) ^ (10 : ℕ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
      _ ≤ (y : ℝ) ^ 10 := pow_le_pow_left₀ (by positivity) h 10
  exact_mod_cast this

/-- One application of Lemma 4.1 in the graph `G - Z`, with the outcomes stated in `G`. -/
lemma step (h d : ℕ) (hh : 0 < h) (hd : 2 ≤ d) {V : Type} [Fintype V] (G : SimpleGraph V)
    (Z : Set V) (A' : Finset V) (hAZ : ∀ a ∈ A', a ∉ Z)
    (hA : IsScattered G (2 * d) (A' : Set V)) (hcard : 4 ^ 5 * (h + 1) ^ 10 ≤ A'.card)
    (hG : ¬ IsShallowInducedMinorOneSubdiv (⊤ : SimpleGraph (Fin h)) G (3 * d) 6) :
    (∃ v : V, v ∉ Z ∧ ∃ C : Finset V, C ⊆ A' ∧ A'.card ≤ C.card ^ 10 ∧
        ∀ x ∈ C, G.edist x v ≤ ((d + 6 : ℕ) : ℕ∞)) ∨
    (∃ B : Finset V, B ⊆ A' ∧ A'.card ≤ B.card ^ 10 ∧
        IsScatteredOff G (2 * (d + 1)) Z (B : Set V)) := by
  classical
  let A'' : Finset ↥Zᶜ := A'.subtype (fun x => x ∈ Zᶜ)
  have hcardA'' : A''.card = A'.card := by
    rw [Finset.card_subtype]
    congr 1
    exact Finset.filter_true_of_mem (fun a ha => hAZ a ha)
  have hmemA'' : ∀ a : ↥Zᶜ, a ∈ A'' ↔ (a : V) ∈ A' := fun a => by
    simp [A'']
  have hsc : IsScattered (G.induce Zᶜ) (2 * d) (A'' : Set ↥Zᶜ) := by
    intro a ha b hb hab
    have ha' : (a : V) ∈ A' := (hmemA'' a).mp ha
    have hb' : (b : V) ∈ A' := (hmemA'' b).mp hb
    have := hA a ha' b hb' (fun h => hab (Subtype.ext h))
    exact lt_of_lt_of_le this (edist_le_induce _ a b)
  have h41 := lemma_4_1 h d hh hd ↥Zᶜ (G.induce Zᶜ) A'' hsc (by rw [hcardA'']; exact hcard)
  rcases h41 with ⟨v, hv⟩ | ⟨B, hBA, hBcard, hBsc⟩ | h3
  · left
    refine ⟨v, v.2, ?_⟩
    let Cs : Finset ↥Zᶜ := A''.filter (fun y => (G.induce Zᶜ).edist y v ≤ ((d + 6 : ℕ) : ℕ∞))
    have hset : ((A'' : Set ↥Zᶜ) ∩ ball (G.induce Zᶜ) {v} (d + 6)) = (Cs : Set ↥Zᶜ) := by
      ext y
      simp [ball, Cs]
    rw [hset, Set.ncard_coe_finset, hcardA''] at hv
    have hv' := nat_of_rpow _ _ hv
    refine ⟨Cs.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact (hmemA'' y).mp (Finset.mem_filter.mp hy).1
    · rw [Finset.card_map]; exact hv'
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact (edist_le_induce _ y v).trans (Finset.mem_filter.mp hy).2
  · right
    refine ⟨B.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact (hmemA'' y).mp (hBA hy)
    · rw [Finset.card_map]
      have := nat_of_rpow _ _ (by rw [hcardA''] at hBcard; exact hBcard)
      exact this
    · intro a b ha hb hab
      obtain ⟨y, hy, hya⟩ := Finset.mem_map.mp (Finset.mem_coe.mp ha)
      obtain ⟨z, hz, hzb⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hb)
      have hya' : y = a := Subtype.ext hya
      have hzb' : z = b := Subtype.ext hzb
      subst hya' hzb'
      exact hBsc y hy z hz hab
  · exfalso
    exact hG (mono_radius _ _ (transfer _ (SimpleGraph.Embedding.induce Zᶜ) _ _ h3) le_rfl
      (by norm_num))

/-- Final stage of Lemma 4.2: `h` vertices `x i` and `h` vertices `v j`, a `2d`-scattered family
and a `37`-scattered one, all pairs within distance `d + 6` but the `x`'s outside the `37`-balls,
give a `(3d, 6)`-shallow induced model of the 1-subdivision of `K_h`. -/
lemma final_stage (h d : ℕ) (hh : 2 ≤ h) {V : Type} (G : SimpleGraph V) (A' X : Finset V)
    (hA' : IsScattered G (2 * d) (A' : Set V)) (hAc : h ≤ A'.card) (hXc : X.card = h)
    (hX : IsScattered G 37 (X : Set V))
    (hB : ∀ a ∈ A', ∀ v ∈ X, G.edist a v ≤ ((d + 6 : ℕ) : ℕ∞))
    (hout : ∀ a ∈ A', ∀ v ∈ X, ((37 : ℕ) : ℕ∞) < G.edist a v) :
    IsShallowInducedMinorOneSubdiv (⊤ : SimpleGraph (Fin h)) G (3 * d) 6 := by
  obtain ⟨fx⟩ : Nonempty (Fin h ↪ ↥A') :=
    Function.Embedding.nonempty_of_card_le (by simpa using hAc)
  obtain ⟨fv⟩ : Nonempty (Fin h ↪ ↥X) :=
    Function.Embedding.nonempty_of_card_le (by simpa [hXc] using le_rfl)
  let i0 : Fin h := ⟨0, by omega⟩
  have hd32 : 32 ≤ d := by
    have h1 := hout _ (fx i0).2 _ (fv i0).2
    have h2 := hB _ (fx i0).2 _ (fv i0).2
    have h3 := lt_of_lt_of_le h1 h2
    have : 37 < d + 6 := by exact_mod_cast h3
    omega
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 32 := ⟨d - 32, by omega⟩
  have hne : ∀ i j, G.edist ((fx i : ↥A') : V) ((fv j : ↥X) : V) ≠ ⊤ := fun i j =>
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) (hB _ (fx i).2 _ (fv j).2)
  have hxx : ∀ i k, i ≠ k →
      ((2 * (e + 32) : ℕ) : ℕ∞) < G.edist ((fx i : ↥A') : V) ((fx k : ↥A') : V) := by
    intro i k hik
    exact hA' _ (fx i).2 _ (fx k).2 (fun h => hik (fx.injective (Subtype.ext h)))
  have hvv : ∀ i k, i ≠ k →
      ((37 : ℕ) : ℕ∞) < G.edist ((fv i : ↥X) : V) ((fv k : ↥X) : V) := by
    intro i k hik
    exact hX _ (fv i).2 _ (fv k).2 (fun h => hik (fv.injective (Subtype.ext h)))
  let L : Fin h → Fin h → ℕ := fun i j => (G.edist ((fx i : ↥A') : V) ((fv j : ↥X) : V)).toNat
  have hL : ∀ i j, G.edist ((fx i : ↥A') : V) ((fv j : ↥X) : V) = L i j := fun i j =>
    (ENat.natCast_toNat (hne i j)).symm
  have hL2 : ∀ i j, L i j ≤ e + 38 := by
    intro i j
    have := hB _ (fx i).2 _ (fv j).2
    rw [hL i j] at this
    exact_mod_cast this
  have hL1 : ∀ i j, e + 27 ≤ L i j := by
    intro i j
    obtain ⟨k, hk⟩ : ∃ k : Fin h, k ≠ i := by
      by_cases h0 : i.val = 0
      · exact ⟨⟨1, by omega⟩, fun h' => by have := congrArg Fin.val h'; simp at this; omega⟩
      · exact ⟨⟨0, by omega⟩, fun h' => by have := congrArg Fin.val h'; simp at this; omega⟩
    have h1 := hxx i k (Ne.symm hk)
    have h2 := hB _ (fx k).2 _ (fv j).2
    have h3 : G.edist ((fx i : ↥A') : V) ((fx k : ↥A') : V) ≤
        G.edist ((fx i : ↥A') : V) ((fv j : ↥X) : V) +
          G.edist ((fv j : ↥X) : V) ((fx k : ↥A') : V) := SimpleGraph.edist_triangle
    rw [hL i j, SimpleGraph.edist_comm (u := ((fv j : ↥X) : V))] at h3
    have h4 := lt_of_lt_of_le h1 (h3.trans (add_le_add_right h2 _))
    have : 2 * (e + 32) < L i j + (e + 32 + 6) := by exact_mod_cast h4
    omega
  have hp : ∀ i j, ∃ p : ℕ → V, p 0 = ((fx i : ↥A') : V) ∧ p (L i j) = ((fv j : ↥X) : V) ∧
      ∀ t, t < L i j → G.Adj (p t) (p (t + 1)) := fun i j => geo_path _ _ _ (hL i j)
  choose p hp0 hpL hpa using hp
  exact model_of_geo
    { x := fun i => ((fx i : ↥A') : V)
      v := fun j => ((fv j : ↥X) : V)
      L := L
      p := p
      hxx := hxx
      hvv := hvv
      hL := hL
      hL1 := hL1
      hL2 := hL2
      hp0 := hp0
      hpL := hpL
      hpa := hpa }

end FatFlat.Dev.L42
end

section
set_option autoImplicit false

namespace FatFlat.Dev.L42
open FatFlat.Hereditary

/-- Invariant of the procedure in the proof of Lemma 4.2. -/
def Inv {V : Type} (G : SimpleGraph V) (A : Finset V) (T h d i : ℕ) (Ai X : Finset V) : Prop :=
  X.card = i ∧ IsScattered G 37 (X : Set V) ∧ T ^ (10 ^ (h - i)) ≤ Ai.card ∧ Ai ⊆ A ∧
    ∀ v ∈ X, ∀ a ∈ Ai, a ∈ ball G {v} (d + 6) ∨ a ∈ ball G (X : Set V) 37

/-- The conclusion of Lemma 4.2. -/
def Goal {V : Type} (G : SimpleGraph V) (A : Finset V) (h d m : ℕ) : Prop :=
  ∃ X : Finset V, X.card ≤ h ∧ ∃ B : Finset V, B ⊆ A ∧ m ≤ B.card ∧
    IsScatteredOff G (2 * (d + 1)) (ball G (X : Set V) 37) (B : Set V)

lemma arith_size (T m S h i a b : ℕ) (hT1 : S ≤ T) (hT2 : m ≤ T) (hS : 2 ≤ S) (hi : i < h)
    (hA : T ^ (10 ^ (h - i)) ≤ a) (hb : b < m) : S + b ≤ a := by
  have h1 : T ^ 10 ≤ T ^ (10 ^ (h - i)) := by
    apply Nat.pow_le_pow_right (by omega)
    exact Nat.le_self_pow (by omega) 10
  have h2 : T ^ 2 ≤ T ^ 10 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h3 : 2 * T ≤ T ^ 2 := by
    rw [pow_two]; exact Nat.mul_le_mul_right T (by omega)
  omega

lemma arith_two (T m h i a a' b c : ℕ) (hT : m ≤ T) (hi : i < h) (hA : T ^ (10 ^ (h - i)) ≤ a)
    (hsum : a' + b = a) (hc : a' ≤ c ^ 10) (hT0 : 1 ≤ T) : m ≤ c + b := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 : T ^ 10 ≤ T ^ (10 ^ (h - i)) := by
    apply Nat.pow_le_pow_right (by omega)
    exact Nat.le_self_pow (by omega) 10
  have h2 : m ^ 10 ≤ T ^ 10 := Nat.pow_le_pow_left hT 10
  have h3 : (c + b) ^ 10 < m ^ 10 := Nat.pow_lt_pow_left hlt (by norm_num)
  have h4 : c ^ 10 + b ^ 10 ≤ (c + b) ^ 10 := pow_add_pow_le (Nat.zero_le _) (Nat.zero_le _) (by norm_num)
  have h5 : b ≤ b ^ 10 := Nat.le_self_pow (by norm_num) b
  omega

lemma arith_one (T h i a a' b c : ℕ) (hi : i + 1 ≤ h) (hA : T ^ (10 ^ (h - i)) ≤ a)
    (hsum : a' + b = a) (hc : a' ≤ c ^ 10) : T ^ (10 ^ (h - (i + 1))) ≤ b + c := by
  have e1 : 10 ^ (h - i) = 10 ^ (h - (i + 1)) * 10 := by
    rw [← pow_succ]; congr 1; omega
  rw [e1, pow_mul] at hA
  have h4 : c ^ 10 + b ^ 10 ≤ (c + b) ^ 10 :=
    pow_add_pow_le (Nat.zero_le _) (Nat.zero_le _) (by norm_num)
  have h5 : b ≤ b ^ 10 := Nat.le_self_pow (by norm_num) b
  have h6 : (T ^ 10 ^ (h - (i + 1))) ^ 10 ≤ (b + c) ^ 10 := by
    rw [add_comm b c]; omega
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h6

lemma ball_mono_set {V : Type} (G : SimpleGraph V) {X Y : Set V} (hXY : X ⊆ Y) (r : ℕ) :
    ball G X r ⊆ ball G Y r := fun _ ⟨z, hz, h⟩ => ⟨z, hXY hz, h⟩

lemma not_mem_ball {V : Type} (G : SimpleGraph V) (X : Finset V) (r : ℕ) (v : V)
    (hv : v ∉ ball G (X : Set V) r) : ∀ z ∈ X, ((r : ℕ) : ℕ∞) < G.edist v z := by
  intro z hz
  by_contra hc
  exact hv ⟨z, hz, not_lt.mp hc⟩

lemma no_edge_one (ε : (⊤ : SimpleGraph (Fin 1)).edgeSet) : False := by
  obtain ⟨s, hs⟩ := ε
  induction s using Sym2.ind with
  | h a b =>
    simp only [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] at hs
    exact hs (Subsingleton.elim a b)

lemma loop (h d m T : ℕ) (hh : 0 < h) (hd : 2 ≤ d) (hm : 0 < m) {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (hG : ¬ IsShallowInducedMinorOneSubdiv (⊤ : SimpleGraph (Fin h)) G (3 * d) 6)
    (A : Finset V) (hA : IsScattered G (2 * d) (A : Set V))
    (hT1 : 4 ^ 5 * (h + 1) ^ 10 ≤ T) (hT2 : m + h - 1 ≤ T) (hAcard : T ^ (10 ^ h) ≤ A.card) :
    ∀ i, i ≤ h → Goal G A h d m ∨ ∃ Ai X : Finset V, Inv G A T h d i Ai X := by
  classical
  have hS2 : 2 ≤ 4 ^ 5 * (h + 1) ^ 10 := by
    have : 1 ≤ (h + 1) ^ 10 := Nat.one_le_pow _ _ (by omega)
    omega
  intro i
  induction i with
  | zero =>
    intro _
    right
    refine ⟨A, ∅, ?_, ?_, ?_, subset_rfl, ?_⟩
    · simp
    · intro a ha; simp at ha
    · simpa using hAcard
    · simp
  | succ i ih =>
    intro hi
    rcases ih (by omega) with hgoal | ⟨Ai, X, hXc, hXs, hAic, hsub, hball⟩
    · left; exact hgoal
    set Z : Set V := ball G (X : Set V) 37 with hZ
    set Bi : Finset V := Ai.filter (fun a => a ∈ Z) with hBi
    set A' : Finset V := Ai.filter (fun a => a ∉ Z) with hA'
    have hsum : Bi.card + A'.card = Ai.card := Finset.card_filter_add_card_filter_not _
    have hBiZ : ∀ a ∈ Bi, a ∈ Z := fun a ha => (Finset.mem_filter.mp ha).2
    have hA'Z : ∀ a ∈ A', a ∉ Z := fun a ha => (Finset.mem_filter.mp ha).2
    have hA'sub : A' ⊆ Ai := Finset.filter_subset _ _
    have hBisub : Bi ⊆ Ai := Finset.filter_subset _ _
    by_cases hmB : m ≤ Bi.card
    · left
      refine ⟨X, by omega, Bi, hBisub.trans hsub, hmB, ?_⟩
      intro a b ha hb _
      exact absurd (hBiZ _ (Finset.mem_coe.mp ha)) a.2
    have hSA : 4 ^ 5 * (h + 1) ^ 10 ≤ A'.card :=
      by have := arith_size T m _ h i Ai.card Bi.card hT1 (by omega) hS2 (by omega) hAic
           (by omega)
         omega
    have hA'sc : IsScattered G (2 * d) (A' : Set V) := fun a ha b hb hab =>
      hA a (by exact_mod_cast (hA'sub.trans hsub) ha) b
        (by exact_mod_cast (hA'sub.trans hsub) hb) hab
    rcases step h d hh hd G Z A' hA'Z hA'sc hSA hG with
      ⟨v, hvZ, C, hCA, hCcard, hCd⟩ | ⟨B, hBA, hBcard, hBsc⟩
    · -- first outcome of Lemma 4.1: a new vertex `v`
      right
      have hdisj : Disjoint Bi C := by
        rw [Finset.disjoint_left]
        intro a haB haC
        exact hA'Z a (hCA haC) (hBiZ a haB)
      have hvX : v ∉ X := fun hv => hvZ ⟨v, hv, by simp⟩
      refine ⟨Bi ∪ C, insert v X, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hvX, hXc]
      · intro a ha b hb hab
        have h37 := not_mem_ball G X 37 v hvZ
        rw [Finset.coe_insert, Set.mem_insert_iff] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd rfl hab
        · exact h37 b hb
        · rw [SimpleGraph.edist_comm]; exact h37 a ha
        · exact hXs a ha b hb hab
      · rw [Finset.card_union_of_disjoint hdisj]
        exact arith_one T h i Ai.card A'.card Bi.card C.card (by omega) hAic
          (by omega) hCcard
      · intro a ha
        rcases Finset.mem_union.mp ha with ha | ha
        · exact hsub (hBisub ha)
        · exact hsub (hA'sub (hCA ha))
      · intro w hw a ha
        rcases Finset.mem_union.mp ha with ha | ha
        · right
          exact ball_mono_set G (by intro z hz; simp [hz]) 37 (hBiZ a ha)
        · rcases Finset.mem_insert.mp hw with rfl | hw
          · left; exact ⟨w, rfl, hCd a ha⟩
          · rcases hball w hw a (hA'sub (hCA ha)) with h1 | h1
            · left; exact h1
            · exact absurd h1 (hA'Z a (hCA ha))
    · -- second outcome of Lemma 4.1: a scattered set
      left
      have hdisj : Disjoint B Bi := by
        rw [Finset.disjoint_left]
        intro a haB haC
        exact hA'Z a (hBA haB) (hBiZ a haC)
      refine ⟨X, by omega, B ∪ Bi, ?_, ?_, ?_⟩
      · intro a ha
        rcases Finset.mem_union.mp ha with ha | ha
        · exact hsub (hA'sub (hBA ha))
        · exact hsub (hBisub ha)
      · rw [Finset.card_union_of_disjoint hdisj]
        have := arith_two T m h i Ai.card A'.card Bi.card B.card (by omega) (by omega) hAic
          (by omega) hBcard (by omega)
        omega
      · intro a b ha hb hab
        have haB : (a : V) ∈ B := by
          rcases Finset.mem_union.mp (Finset.mem_coe.mp ha) with h1 | h1
          · exact h1
          · exact absurd (hBiZ _ h1) a.2
        have hbB : (b : V) ∈ B := by
          rcases Finset.mem_union.mp (Finset.mem_coe.mp hb) with h1 | h1
          · exact h1
          · exact absurd (hBiZ _ h1) b.2
        exact hBsc a b haB hbB hab

end FatFlat.Dev.L42

namespace FatFlat.Hereditary
open FatFlat.Dev.L42 in
theorem chk_lemma_4_2 (h d m : ℕ) (hh : 0 < h) (hd : 2 ≤ d) (hm : 0 < m) (V : Type) [Fintype V]
    (G : SimpleGraph V)
    (hG : ¬ IsShallowInducedMinorOneSubdiv (⊤ : SimpleGraph (Fin h)) G (3 * d) 6)
    (A : Finset V) (hA : IsScattered G (2 * d) (A : Set V))
    (hAcard : (max (4 ^ 5 * (h + 1) ^ 10) (m + h - 1)) ^ (10 ^ h) ≤ A.card) :
    ∃ X : Finset V, X.card ≤ h ∧ ∃ B : Finset V, B ⊆ A ∧ m ≤ B.card ∧
      IsScatteredOff G (2 * (d + 1)) (ball G (X : Set V) 37) (B : Set V) := by
  classical
  have hT1 : 4 ^ 5 * (h + 1) ^ 10 ≤ max (4 ^ 5 * (h + 1) ^ 10) (m + h - 1) := le_max_left _ _
  have hT2 : m + h - 1 ≤ max (4 ^ 5 * (h + 1) ^ 10) (m + h - 1) := le_max_right _ _
  have hS2 : 2 ≤ 4 ^ 5 * (h + 1) ^ 10 := by
    have : 1 ≤ (h + 1) ^ 10 := Nat.one_le_pow _ _ (by omega)
    omega
  set T := max (4 ^ 5 * (h + 1) ^ 10) (m + h - 1) with hT
  by_cases h1 : h = 1
  · -- the 1-subdivision of `K_1` is a single vertex
    subst h1
    exfalso
    have hApos : 0 < A.card := by
      have : 1 ≤ T ^ (10 ^ 1) := Nat.one_le_pow _ _ (by omega)
      omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hApos
    refine hG (mkModel _ G _ 6 (fun _ => {a}) (fun ε => (no_edge_one ε).elim) ?_ ?_ ?_ ?_ ?_ ?_)
    · intro u; exact ⟨⟨a, rfl⟩, by rintro ⟨y, rfl⟩; simp⟩
    · intro ε; exact (no_edge_one ε).elim
    · intro u u' huu; exact absurd (Subsingleton.elim u u') huu
    · intro ε; exact (no_edge_one ε).elim
    · intro u ε; exact (no_edge_one ε).elim
    · intro u ε; exact (no_edge_one ε).elim
  have h2 : 2 ≤ h := by omega
  rcases loop h d m T hh hd hm G hG A hA hT1 hT2 hAcard h le_rfl with hgoal | ⟨Ai, X, hXc, hXs, hAic, hsub, hball⟩
  · exact hgoal
  set Z : Set V := ball G (X : Set V) 37 with hZ
  set Bi : Finset V := Ai.filter (fun a => a ∈ Z) with hBi
  set A' : Finset V := Ai.filter (fun a => a ∉ Z) with hA'
  have hsum : Bi.card + A'.card = Ai.card := Finset.card_filter_add_card_filter_not _
  have hBiZ : ∀ a ∈ Bi, a ∈ Z := fun a ha => (Finset.mem_filter.mp ha).2
  have hA'Z : ∀ a ∈ A', a ∉ Z := fun a ha => (Finset.mem_filter.mp ha).2
  have hA'sub : A' ⊆ Ai := Finset.filter_subset _ _
  have hBisub : Bi ⊆ Ai := Finset.filter_subset _ _
  by_cases hmB : m ≤ Bi.card
  · refine ⟨X, by omega, Bi, hBisub.trans hsub, hmB, ?_⟩
    intro a b ha hb _
    exact absurd (hBiZ _ (Finset.mem_coe.mp ha)) a.2
  exfalso
  have hAh : T ≤ Ai.card := by simpa using hAic
  have hAcardh : h ≤ A'.card := by omega
  have hA'sc : IsScattered G (2 * d) (A' : Set V) := fun a ha b hb hab =>
    hA a (by exact_mod_cast (hA'sub.trans hsub) ha) b
      (by exact_mod_cast (hA'sub.trans hsub) hb) hab
  have hX37 : ∀ a ∈ A', ∀ v ∈ X, ((37 : ℕ) : ℕ∞) < G.edist a v := fun a ha =>
    not_mem_ball G X 37 a (hA'Z a ha)
  refine hG (final_stage h d h2 G A' X hA'sc hAcardh hXc hXs ?_ hX37)
  intro a ha v hv
  rcases hball v hv a (hA'sub ha) with h1 | h1
  · obtain ⟨z, hz, hzd⟩ := h1
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hzd
  · exact absurd h1 (hA'Z a ha)

end FatFlat.Hereditary
end

theorem solution : type_of% @FatFlat.Hereditary.chk_lemma_4_2 := @FatFlat.Hereditary.chk_lemma_4_2
