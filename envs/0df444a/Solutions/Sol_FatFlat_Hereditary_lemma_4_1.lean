-- Prove2me | solution 1 for FatFlat.Hereditary.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:39:20.828515+00:00
-- url     : https://prove2.me/submissions/1bd70742-92f0-4956-9bfc-e2089cba14ab

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Classes
import Theorems.Thm_FatFlat_Hereditary_theorem_2_1

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

lemma Far.mono {S S' T T' : Set V} (h : Far G S T) (hS : S' ⊆ S) (hT : T' ⊆ T) : Far G S' T' :=
  fun x hx y hy => h x (hS hx) y (hT hy)

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

namespace FatFlat.Dev.L41

/-- Greedy independent set: if every vertex of `S` has at most `Δ` neighbours in `S`, then `S`
has an independent subset `I` with `|S| ≤ |I| (Δ+1)`. -/
lemma greedy {ι : Type} [DecidableEq ι] (R : ι → ι → Prop) [DecidableRel R]
    (hsymm : ∀ a b, R a b → R b a) (Δ : ℝ) :
    ∀ S : Finset ι, (∀ v ∈ S, ((S.filter (R v)).card : ℝ) ≤ Δ) →
      ∃ I : Finset ι, I ⊆ S ∧ (∀ a ∈ I, ∀ b ∈ I, a ≠ b → ¬ R a b) ∧
        (S.card : ℝ) ≤ I.card * (Δ + 1) := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hdeg
    rcases S.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · exact ⟨∅, by simp, by simp, by simp⟩
    · set S' : Finset ι := S.filter (fun w => w ≠ v ∧ ¬ R v w) with hS'
      have hsub : S' ⊂ S := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
        intro h
        have : v ∈ S' := h ▸ hv
        simp [hS'] at this
      have hdeg' : ∀ w ∈ S', ((S'.filter (R w)).card : ℝ) ≤ Δ := by
        intro w hw
        refine le_trans ?_ (hdeg w (hsub.subset hw))
        exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hsub.subset)
      obtain ⟨I', hI'S, hI'ind, hI'card⟩ := ih S' hsub hdeg'
      have hvI : v ∉ I' := fun h => by
        have := hI'S h
        simp [hS'] at this
      refine ⟨insert v I', ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hv
        · exact hsub.subset (hI'S hx)
      · have hv' : ∀ b ∈ I', ¬ R v b := fun b hb => by
          have := hI'S hb
          simp only [hS', Finset.mem_filter] at this
          exact this.2.2
        intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with rfl | ha' <;> rcases Finset.mem_insert.mp hb with rfl | hb'
        · exact absurd rfl hab
        · exact hv' b hb'
        · exact fun h => hv' a ha' (hsymm _ _ h)
        · exact hI'ind a ha' b hb' hab
      · have hcover : S \ S' ⊆ insert v (S.filter (R v)) := by
          intro x hx
          simp only [Finset.mem_sdiff, hS', Finset.mem_filter, not_and, not_not] at hx
          by_cases hxv : x = v
          · simp [hxv]
          · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hx.1, hx.2 hx.1 hxv⟩)
        have h1 : ((S \ S').card : ℝ) ≤ Δ + 1 := by
          have := Finset.card_le_card hcover
          have h2 : ((insert v (S.filter (R v))).card : ℝ) ≤ (S.filter (R v)).card + 1 := by
            exact_mod_cast Finset.card_insert_le _ _
          have h3 := hdeg v hv
          have : ((S \ S').card : ℝ) ≤ ((insert v (S.filter (R v))).card : ℝ) := by exact_mod_cast this
          linarith
        have h4 : (S.card : ℝ) = S'.card + (S \ S').card := by
          have := Finset.card_sdiff_add_card_eq_card hsub.subset
          rw [← this]; push_cast; ring
        rw [Finset.card_insert_of_notMem hvI]
        push_cast
        nlinarith

end FatFlat.Dev.L41
end

section
set_option autoImplicit false

namespace FatFlat.Dev.L41
open FatFlat.Hereditary FatFlat.Dev.L42

section Reach
variable {V : Type} {G : SimpleGraph V}

/-- `Reach G S a b n`: a walk of length at most `n` from `a` to `b` inside `S`. -/
def Reach (G : SimpleGraph V) (S : Set V) (a b : V) (n : ℕ) : Prop :=
  ∃ p : ℕ → V, ∃ m, m ≤ n ∧ p 0 = a ∧ p m = b ∧ (∀ t, t ≤ m → p t ∈ S) ∧
    ∀ t, t < m → G.Adj (p t) (p (t + 1))

lemma Reach.mono_set {S S' : Set V} {a b : V} {n : ℕ} (h : Reach G S a b n) (hS : S ⊆ S') :
    Reach G S' a b n := by
  obtain ⟨p, m, hm, h0, h1, h2, h3⟩ := h
  exact ⟨p, m, hm, h0, h1, fun t ht => hS (h2 t ht), h3⟩

lemma Reach.mono_n {S : Set V} {a b : V} {n n' : ℕ} (h : Reach G S a b n) (hn : n ≤ n') :
    Reach G S a b n' := by
  obtain ⟨p, m, hm, h0, h1, h2, h3⟩ := h
  exact ⟨p, m, hm.trans hn, h0, h1, h2, h3⟩

lemma Reach.symm {S : Set V} {a b : V} {n : ℕ} (h : Reach G S a b n) : Reach G S b a n := by
  obtain ⟨p, m, hm, h0, h1, h2, h3⟩ := h
  refine ⟨fun t => p (m - t), m, hm, by simpa using h1, by simpa using h0,
    fun t ht => h2 _ (by omega), fun t ht => ?_⟩
  have := (h3 (m - (t + 1)) (by omega)).symm
  have e : m - (t + 1) + 1 = m - t := by omega
  rw [e] at this
  exact this

lemma Reach.trans {S : Set V} {a b c : V} {n n' : ℕ} (h : Reach G S a b n)
    (h' : Reach G S b c n') : Reach G S a c (n + n') := by
  obtain ⟨p, m, hm, h0, h1, h2, h3⟩ := h
  obtain ⟨q, m', hm', h0', h1', h2', h3'⟩ := h'
  refine ⟨fun t => if t ≤ m then p t else q (t - m), m + m', by omega, ?_, ?_, ?_, ?_⟩
  · simp [h0]
  · by_cases hm0 : m' = 0
    · subst hm0
      simp only [add_zero, le_refl, if_true]
      rw [h1, ← h0']; exact h1'
    · have : ¬ (m + m' ≤ m) := by omega
      simp only [this, if_false, Nat.add_sub_cancel_left]; exact h1'
  · intro t ht
    by_cases htm : t ≤ m
    · simp only [htm, if_true]; exact h2 t htm
    · simp only [htm, if_false]; exact h2' _ (by omega)
  · intro t ht
    by_cases htm : t < m
    · have h1 : t ≤ m := htm.le
      have h2 : t + 1 ≤ m := htm
      simp only [h1, h2, if_true]; exact h3 t htm
    · have ht' : t = m ∨ m < t := by omega
      rcases ht' with rfl | ht'
      · simp only [le_refl, if_true, Nat.add_sub_cancel_left]
        have : ¬ (t + 1 ≤ t) := by omega
        simp only [this, if_false, Nat.add_sub_cancel_left]
        rw [h1, ← h0']
        exact h3' 0 (by omega)
      · have h1 : ¬ t ≤ m := by omega
        have h2 : ¬ t + 1 ≤ m := by omega
        simp only [h1, h2, if_false]
        have e : t + 1 - m = (t - m) + 1 := by omega
        rw [e]
        exact h3' _ (by omega)

lemma Reach.edist {S : Set V} {a b : V} {n : ℕ} (h : Reach G S a b n) (ha : a ∈ S) (hb : b ∈ S) :
    (G.induce S).edist ⟨a, ha⟩ ⟨b, hb⟩ ≤ n := by
  obtain ⟨p, m, hm, h0, h1, h2, h3⟩ := h
  subst h0 h1
  have := path_edist (G := G) S p 0 m (fun u _ hu => h2 u (by omega)) (fun u _ hu => h3 u (by omega))
  refine le_trans ?_ (by exact_mod_cast hm : (m : ℕ∞) ≤ n)
  simpa using this

lemma reach_radius {S : Set V} {c : V} (hc : c ∈ S) {r : ℕ}
    (h : ∀ v ∈ S, Reach G S c v r) : RadiusLE G S r :=
  ⟨⟨c, hc⟩, fun v => (h v v.2).edist hc v.2⟩

/-- a segment of a path function -/
lemma reach_seg (p : ℕ → V) (L : ℕ) (hadj : ∀ t, t < L → G.Adj (p t) (p (t + 1)))
    (S : Set V) (a b : ℕ) (hab : a ≤ b) (hb : b ≤ L) (hS : ∀ t, a ≤ t → t ≤ b → p t ∈ S) :
    Reach G S (p a) (p b) (b - a) := by
  refine ⟨fun t => p (a + t), b - a, le_rfl, by simp, by simp [Nat.add_sub_cancel' hab],
    fun t ht => hS _ (by omega) (by omega), fun t ht => ?_⟩
  have := hadj (a + t) (by omega)
  simpa [Nat.add_assoc] using this

/-- a point at distance `k ≤ r` of `x` is reached inside any set containing the `r`-ball. -/
lemma reach_ball {S : Set V} {x u : V} {r : ℕ} (hS : ∀ w, G.edist w x ≤ r → w ∈ S)
    (hu : G.edist x u ≤ r) : Reach G S x u r := by
  obtain ⟨k, hk, hkr⟩ := enat_nat _ r hu
  obtain ⟨p, h0, hL, hadj⟩ := geo_path x u k hk
  have h1 := reach_seg p k hadj S 0 k (Nat.zero_le _) le_rfl (fun t _ ht => by
    apply hS
    have := (geo_exact p k (by rw [h0, hL]; exact hk) hadj t ht).1
    rw [h0] at this
    rw [SimpleGraph.edist_comm, this]
    exact_mod_cast (by omega : t ≤ r))
  rw [h0, hL, Nat.sub_zero] at h1
  exact h1.mono_n hkr

end Reach

end FatFlat.Dev.L41
end

section
set_option autoImplicit false

namespace FatFlat.Dev.L41
open FatFlat.Hereditary FatFlat.Dev.L42

section Mid
variable {V : Type} (G : SimpleGraph V)

/-- the closed ball of radius `r` around `x` -/
def Bl (x : V) (r : ℕ) : Set V := {u | G.edist u x ≤ r}

lemma gpath_ex (x y : V) : ∃ q : ℕ → V, ∀ L : ℕ, G.edist x y = L →
    q 0 = x ∧ q L = y ∧ ∀ t, t < L → G.Adj (q t) (q (t + 1)) := by
  by_cases hex : ∃ L0 : ℕ, G.edist x y = L0
  · obtain ⟨L0, h0⟩ := hex
    obtain ⟨q, hq0, hqL, hqa⟩ := geo_path x y L0 h0
    refine ⟨q, fun L hL => ?_⟩
    have : L = L0 := by rw [h0] at hL; exact_mod_cast hL.symm
    subst this
    exact ⟨hq0, hqL, hqa⟩
  · exact ⟨fun _ => x, fun L hL => absurd ⟨L, hL⟩ hex⟩

/-- a chosen geodesic from `x` to `y` -/
noncomputable def gpath (x y : V) : ℕ → V := (gpath_ex (G := G) x y).choose

lemma gpath_spec (x y : V) (L : ℕ) (h : G.edist x y = L) :
    gpath G x y 0 = x ∧ gpath G x y L = y ∧ ∀ t, t < L → G.Adj (gpath G x y t) (gpath G x y (t + 1)) :=
  (gpath_ex (G := G) x y).choose_spec L h

/-- the middle part of the geodesic -/
def Mset (d : ℕ) (x y : V) : Set V :=
  {v | ∃ t, d - 1 ≤ t ∧ t + d ≤ (G.edist x y).toNat + 1 ∧ v = gpath G x y t}

variable {G}

lemma ge_succ {n : ℕ} {x : ℕ∞} (h : ((n : ℕ) : ℕ∞) < x) : ((n + 1 : ℕ) : ℕ∞) ≤ x := by
  have := Order.add_one_le_of_lt h
  exact_mod_cast this

/-- properties of the middle part of a geodesic of length `L ∈ {2d+1, 2d+2}`. -/
lemma mset_props (d : ℕ) (hd : 2 ≤ d) (x y : V) (L : ℕ) (hL : G.edist x y = L)
    (hL1 : 2 * d + 1 ≤ L) (hL2 : L ≤ 2 * d + 2) :
    let M := Mset G d x y
    -- (a)
    (M ⊆ Bl G x (d + 1) ∪ Bl G y (d + 1)) ∧
    (Disjoint (Bl G x (d - 2)) M ∧ ∃ p ∈ Bl G x (d - 2), ∃ q ∈ M, G.Adj p q) ∧
    (Disjoint (Bl G y (d - 2)) M ∧ ∃ p ∈ Bl G y (d - 2), ∃ q ∈ M, G.Adj p q) ∧
    Reach G (Bl G x (d - 2) ∪ M ∪ Bl G y (d - 2)) x y (2 * d + 2) ∧
    RadiusLE G M 2 ∧
    (∃ m, (∀ t ∈ M, G.edist t m ≤ 2) ∧ G.edist x m ≤ d + 1 ∧ G.edist y m ≤ d + 1) ∧
    (∀ v ∈ M, Reach G (Bl G x (d - 2) ∪ M ∪ Bl G y (d - 2)) x v (2 * d + 2) ∧
      Reach G (Bl G x (d - 2) ∪ M ∪ Bl G y (d - 2)) y v (2 * d + 2)) := by
  intro M
  obtain ⟨h0, hLy, hadj⟩ := gpath_spec G x y L hL
  set p := gpath G x y with hp
  have hex := geo_exact p L (by rw [h0, hLy]; exact hL) hadj
  have hxd : ∀ t, t ≤ L → G.edist (p t) x = t := fun t ht => by
    rw [SimpleGraph.edist_comm, ← h0]; exact (hex t ht).1
  have hyd : ∀ t, t ≤ L → G.edist (p t) y = ((L - t : ℕ) : ℕ∞) := fun t ht => by
    rw [← hLy]; exact (hex t ht).2
  have hLn : (G.edist x y).toNat = L := by rw [hL]; rfl
  have hMmem : ∀ t, d - 1 ≤ t → t + d ≤ L + 1 → p t ∈ M := fun t h1 h2 =>
    ⟨t, h1, by rw [hLn]; exact h2, rfl⟩
  have hMel : ∀ v ∈ M, ∃ t, d - 1 ≤ t ∧ t + d ≤ L + 1 ∧ v = p t := by
    rintro v ⟨t, h1, h2, rfl⟩
    exact ⟨t, h1, by rw [hLn] at h2; exact h2, rfl⟩
  have pos : ∀ s t, s ≤ t → t ≤ L → G.edist (p s) (p t) ≤ ((t - s : ℕ) : ℕ∞) := by
    intro s t hst htL
    have := path_edist_G (G := G) p s (t - s) (fun u _ hu => hadj u (by omega))
    rwa [Nat.add_sub_cancel' hst] at this
  have pos' : ∀ s t, s ≤ L → t ≤ L → G.edist (p s) (p t) ≤ ((max s t - min s t : ℕ) : ℕ∞) := by
    intro s t hs ht
    rcases le_total s t with h | h
    · rw [max_eq_right h, min_eq_left h]; exact pos s t h ht
    · rw [max_eq_left h, min_eq_right h, SimpleGraph.edist_comm]; exact pos t s h hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨t, h1, h2, rfl⟩ := hMel v hv
    by_cases ht : t ≤ d + 1
    · left; show G.edist (p t) x ≤ _; rw [hxd t (by omega)]; exact_mod_cast ht
    · right; show G.edist (p t) y ≤ _; rw [hyd t (by omega)]; exact_mod_cast (by omega : L - t ≤ d + 1)
  · refine ⟨?_, p (d - 2), ?_, p (d - 1), hMmem _ le_rfl (by omega), ?_⟩
    · rw [Set.disjoint_left]
      intro v hv hvM
      obtain ⟨t, h1, h2, rfl⟩ := hMel v hvM
      have : G.edist (p t) x ≤ ((d - 2 : ℕ) : ℕ∞) := hv
      rw [hxd t (by omega)] at this
      have : t ≤ d - 2 := by exact_mod_cast this
      omega
    · show G.edist (p (d - 2)) x ≤ _
      rw [hxd _ (by omega)]
    · have := hadj (d - 2) (by omega)
      have e : d - 2 + 1 = d - 1 := by omega
      rwa [e] at this
  · refine ⟨?_, p (L - d + 2), ?_, p (L - d + 1), hMmem _ (by omega) (by omega), ?_⟩
    · rw [Set.disjoint_left]
      intro v hv hvM
      obtain ⟨t, h1, h2, rfl⟩ := hMel v hvM
      have : G.edist (p t) y ≤ ((d - 2 : ℕ) : ℕ∞) := hv
      rw [hyd t (by omega)] at this
      have : L - t ≤ d - 2 := by exact_mod_cast this
      omega
    · show G.edist (p (L - d + 2)) y ≤ _
      rw [hyd _ (by omega)]
      exact_mod_cast (by omega : L - (L - d + 2) ≤ d - 2)
    · have := (hadj (L - d + 1) (by omega)).symm
      have e : L - d + 1 + 1 = L - d + 2 := by omega
      rwa [e] at this
  · have := reach_seg p L hadj (Bl G x (d - 2) ∪ M ∪ Bl G y (d - 2)) 0 L (Nat.zero_le _) le_rfl
      (by
        intro t _ ht
        by_cases h1 : t ≤ d - 2
        · left; left; show G.edist (p t) x ≤ _; rw [hxd t ht]; exact_mod_cast h1
        · by_cases h2 : t + d ≤ L + 1
          · left; right; exact hMmem t (by omega) h2
          · right; show G.edist (p t) y ≤ _; rw [hyd t ht]
            exact_mod_cast (by omega : L - t ≤ d - 2))
    rw [h0, hLy, Nat.sub_zero] at this
    exact this.mono_n (by omega)
  · have hm : p (d + 1) ∈ M := hMmem _ (by omega) (by omega)
    refine reach_radius hm (fun v hv => ?_)
    obtain ⟨t, h1, h2, rfl⟩ := hMel v hv
    rcases le_total t (d + 1) with h | h
    · have := reach_seg p L hadj M t (d + 1) h (by omega)
        (fun u hu1 hu2 => hMmem u (by omega) (by omega))
      exact this.symm.mono_n (by omega)
    · have := reach_seg p L hadj M (d + 1) t h (by omega)
        (fun u hu1 hu2 => hMmem u (by omega) (by omega))
      exact this.mono_n (by omega)
  · refine ⟨p (d + 1), ?_, ?_, ?_⟩
    · intro v hv
      obtain ⟨t, h1, h2, rfl⟩ := hMel v hv
      refine (pos' t (d + 1) (by omega) (by omega)).trans ?_
      exact_mod_cast (by omega : max t (d + 1) - min t (d + 1) ≤ 2)
    · have := pos' 0 (d + 1) (by omega) (by omega)
      rw [h0] at this
      refine this.trans ?_
      exact_mod_cast (by omega : max 0 (d + 1) - min 0 (d + 1) ≤ d + 1)
    · have := pos' L (d + 1) le_rfl (by omega)
      rw [hLy] at this
      refine this.trans ?_
      exact_mod_cast (by omega : max L (d + 1) - min L (d + 1) ≤ d + 1)
  · intro v hv
    obtain ⟨t, h1, h2, rfl⟩ := hMel v hv
    have hS : ∀ u, u ≤ L → p u ∈ Bl G x (d - 2) ∪ M ∪ Bl G y (d - 2) := by
      intro u hu
      by_cases h1 : u ≤ d - 2
      · left; left; show G.edist (p u) x ≤ _; rw [hxd u hu]; exact_mod_cast h1
      · by_cases h2 : u + d ≤ L + 1
        · left; right; exact hMmem u (by omega) h2
        · right; show G.edist (p u) y ≤ _; rw [hyd u hu]
          exact_mod_cast (by omega : L - u ≤ d - 2)
    constructor
    · have := reach_seg p L hadj (Bl G x (d - 2) ∪ M ∪ Bl G y (d - 2)) 0 t (Nat.zero_le _)
        (by omega) (fun u _ hu => hS u (by omega))
      rw [h0, Nat.sub_zero] at this
      exact this.mono_n (by omega)
    · have := reach_seg p L hadj (Bl G x (d - 2) ∪ M ∪ Bl G y (d - 2)) t L (by omega)
        le_rfl (fun u hu _ => hS u (by omega))
      rw [hLy] at this
      exact this.symm.mono_n (by omega)

end Mid

end FatFlat.Dev.L41
end

section
set_option autoImplicit false

namespace FatFlat.Dev.L41
open FatFlat.Hereditary FatFlat.Dev.L42

section Props
variable {V : Type} (G : SimpleGraph V)

/-- the middle part of a chosen geodesic between the ends of the unordered pair `e` -/
noncomputable def Mv (d : ℕ) (e : Sym2 V) : Set V :=
  Mset G d (Quot.out e).1 (Quot.out e).2

/-- the closed `r`-neighbourhood of the ends of `e` -/
def Sb (r : ℕ) (e : Sym2 V) : Set V := {u | ∃ w ∈ e, G.edist u w ≤ r}

/-- `e` is a pair of distinct vertices of `A` at distance at most `2d+2` -/
def IsEdg (d : ℕ) (A : Set V) (e : Sym2 V) : Prop :=
  ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ G.edist x y ≤ ((2 * d + 2 : ℕ) : ℕ∞) ∧ e = s(x, y)

variable {G}

lemma isEdg_out {d : ℕ} {A : Set V} {e : Sym2 V} (he : IsEdg G d A e) :
    (Quot.out e).1 ∈ A ∧ (Quot.out e).2 ∈ A ∧ (Quot.out e).1 ≠ (Quot.out e).2 ∧
      G.edist (Quot.out e).1 (Quot.out e).2 ≤ ((2 * d + 2 : ℕ) : ℕ∞) ∧
      e = s((Quot.out e).1, (Quot.out e).2) := by
  obtain ⟨x, hx, y, hy, hxy, hd, rfl⟩ := he
  have hq : s(x, y) = s((Quot.out s(x, y)).1, (Quot.out s(x, y)).2) := (Quot.out_eq _).symm
  generalize (Quot.out s(x, y)) = q at hq
  obtain ⟨a, b⟩ := q
  simp only at hq ⊢
  rcases Sym2.eq_iff.mp hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hx, hy, hxy, hd, rfl⟩
  · exact ⟨hy, hx, hxy.symm, by rwa [SimpleGraph.edist_comm], Sym2.eq_swap⟩

lemma isEdg_ne {d : ℕ} {A : Set V} {u w : V} (he : IsEdg G d A s(u, w)) : u ≠ w := by
  obtain ⟨x, hx, y, hy, hxy, hd, h⟩ := he
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hxy
  · exact hxy.symm

lemma Mv_props (d : ℕ) (hd : 2 ≤ d) (A : Set V)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ((2 * d : ℕ) : ℕ∞) < G.edist a b)
    (e : Sym2 V) (he : IsEdg G d A e) :
    RadiusLE G (Mv G d e) 2 ∧
    (∀ z ∈ A, z ∉ e → Far G (Bl G z (d - 2)) (Mv G d e)) ∧
    (∀ x ∈ e, Disjoint (Bl G x (d - 2)) (Mv G d e) ∧
      ∃ p ∈ Bl G x (d - 2), ∃ q ∈ Mv G d e, G.Adj p q) ∧
    (∀ x ∈ e, ∀ y ∈ e, x ≠ y → Reach G (Sb G (d - 2) e ∪ Mv G d e) x y (2 * d + 2)) ∧
    (∀ x ∈ e, ∀ v ∈ Mv G d e, Reach G (Sb G (d - 2) e ∪ Mv G d e) x v (2 * d + 2)) ∧
    (∃ m, (∀ t ∈ Mv G d e, G.edist t m ≤ 2) ∧ ∀ u ∈ e, G.edist u m ≤ d + 1) := by
  obtain ⟨ha, hb, hab, hdist, hq⟩ := isEdg_out he
  set a := (Quot.out e).1 with hadef
  set b := (Quot.out e).2 with hbdef
  have hlt := hA a ha b hb hab
  obtain ⟨L, hL, hLle⟩ := enat_nat _ _ hdist
  have hL1 : 2 * d + 1 ≤ L := by
    rw [hL] at hlt
    exact_mod_cast hlt
  obtain ⟨hM1, hM2, hM3, hM4, hM5, hM6, hM7⟩ := mset_props d hd a b L hL hL1 hLle
  have hMv : Mv G d e = Mset G d a b := rfl
  rw [hMv]
  have hmem : ∀ x, x ∈ e ↔ x = a ∨ x = b := fun x => by
    rw [hq]; exact Sym2.mem_iff
  have hSb : Bl G a (d - 2) ∪ Mset G d a b ∪ Bl G b (d - 2) ⊆ Sb G (d - 2) e ∪ Mset G d a b := by
    rintro v ((hv | hv) | hv)
    · exact Or.inl ⟨a, (hmem a).2 (Or.inl rfl), hv⟩
    · exact Or.inr hv
    · exact Or.inl ⟨b, (hmem b).2 (Or.inr rfl), hv⟩
  refine ⟨hM5, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz hze
    have hza : z ≠ a := fun h => hze ((hmem z).2 (Or.inl h))
    have hzb : z ≠ b := fun h => hze ((hmem z).2 (Or.inr h))
    have h1 := hA z hz a ha hza
    have h2 := hA z hz b hb hzb
    have f1 : Far G (Bl G z (d - 2)) (Bl G a (d + 1)) :=
      far_of_balls (a := z) (b := a) (r := d - 2) (s := d + 1) (fun w hw => hw) (fun w hw => hw)
        (by
          have := ge_succ h1
          refine le_trans ?_ this
          exact_mod_cast (by omega : d - 2 + (d + 1) + 2 ≤ 2 * d + 1))
    have f2 : Far G (Bl G z (d - 2)) (Bl G b (d + 1)) :=
      far_of_balls (a := z) (b := b) (r := d - 2) (s := d + 1) (fun w hw => hw) (fun w hw => hw)
        (by
          have := ge_succ h2
          refine le_trans ?_ this
          exact_mod_cast (by omega : d - 2 + (d + 1) + 2 ≤ 2 * d + 1))
    exact (f1.union_right f2).mono (fun _ h => h) hM1
  · intro x hx
    rcases (hmem x).1 hx with rfl | rfl
    · exact hM2
    · exact hM3
  · intro x hx y hy hxy
    rcases (hmem x).1 hx with rfl | rfl <;> rcases (hmem y).1 hy with rfl | rfl
    · exact absurd rfl hxy
    · exact hM4.mono_set hSb |>.mono_n le_rfl
    · exact (hM4.mono_set hSb).symm
    · exact absurd rfl hxy
  · intro x hx v hv
    rcases (hmem x).1 hx with rfl | rfl
    · exact ((hM7 v hv).1).mono_set hSb
    · exact ((hM7 v hv).2).mono_set hSb
  · obtain ⟨m, hm1, hm2, hm3⟩ := hM6
    refine ⟨m, hm1, fun u hu => ?_⟩
    rcases (hmem u).1 hu with rfl | rfl
    · exact hm2
    · exact hm3

end Props

end FatFlat.Dev.L41
end

section
set_option autoImplicit false

namespace FatFlat.Dev.L41
open FatFlat.Hereditary FatFlat.Dev.L42

section Compose
variable {V : Type}

/-- the graph on `A` whose edges are the pairs in `J` -/
def HJ (J : Set (Sym2 V)) (A : Finset V) : SimpleGraph ↥A where
  Adj a b := a ≠ b ∧ s((a : V), (b : V)) ∈ J
  symm := ⟨fun a b ⟨h, hj⟩ => ⟨h.symm, by rwa [Sym2.eq_swap]⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

lemma HJ_adj (J : Set (Sym2 V)) (A : Finset V) (a b : ↥A) :
    (HJ J A).Adj a b ↔ a ≠ b ∧ s((a : V), (b : V)) ∈ J := Iff.rfl

variable {G : SimpleGraph V}

lemma center_adj {J : Set (Sym2 V)} {A : Finset V} {S : Set ↥A} {c : ↥S}
    (hc : ∀ v : ↥S, ((HJ J A).induce S).edist c v ≤ 1) (v : ↥S) :
    c = v ∨ (HJ J A).Adj c.1 v.1 := by
  by_cases hcv : c = v
  · exact Or.inl hcv
  · right
    have h1 := hc v
    have h0 : ((HJ J A).induce S).edist c v ≠ 0 := by
      rw [Ne, SimpleGraph.edist_eq_zero_iff]; exact hcv
    obtain ⟨k, hk, hk1⟩ := enat_nat _ 1 h1
    have : k = 1 := by
      rcases Nat.lt_or_ge k 1 with h | h
      · exfalso; apply h0; rw [hk]; have : k = 0 := by omega
        rw [this]; rfl
      · omega
    rw [this] at hk
    have := (SimpleGraph.edist_eq_one_iff_adj).mp (by rw [hk]; rfl)
    simpa using this

theorem compose (d h : ℕ) (hd : 2 ≤ d) (A : Finset V)
    (hA : ∀ a ∈ (A : Set V), ∀ b ∈ (A : Set V), a ≠ b → ((2 * d : ℕ) : ℕ∞) < G.edist a b)
    (J : Set (Sym2 V)) (hJE : ∀ e ∈ J, IsEdg G d (A : Set V) e)
    (hJind : ∀ e ∈ J, ∀ f ∈ J, e ≠ f → Far G (Mv G d e) (Mv G d f))
    (hmin : IsShallowMinor (⊤ : SimpleGraph (Fin h)) (HJ J A) 1) :
    IsShallowInducedMinorOneSubdiv (⊤ : SimpleGraph (Fin h)) G (3 * d) 2 := by
  obtain ⟨M2, hrad⟩ := hmin
  set Z : Fin h → Set V := fun k => Subtype.val '' M2.B k with hZdef
  have hZA : ∀ k, ∀ u ∈ Z k, u ∈ (A : Set V) := by
    rintro k u ⟨a, -, rfl⟩
    exact a.2
  have hZd : ∀ i j, i ≠ j → ∀ u, u ∈ Z i → u ∈ Z j → False := by
    rintro i j hij u ⟨a, ha, rfl⟩ ⟨a', ha', h'⟩
    have : a' = a := Subtype.ext h'
    subst this
    exact Set.disjoint_left.mp (M2.disjoint hij) ha ha'
  have hc : ∀ k, ∃ c ∈ Z k, ∀ v ∈ Z k, v = c ∨ s(c, v) ∈ J := by
    intro k
    obtain ⟨c, hcc⟩ := hrad k
    refine ⟨c.1.1, ⟨c.1, c.2, rfl⟩, ?_⟩
    rintro v ⟨a, ha, rfl⟩
    rcases center_adj hcc ⟨a, ha⟩ with h1 | h1
    · left
      have := congrArg (fun x : ↥(M2.B k) => (x.1 : V)) h1
      exact this.symm
    · right; exact h1.2
  choose c hcZ hcJ using hc
  have hch : ∀ ε : (⊤ : SimpleGraph (Fin h)).edgeSet, ∃ e ∈ J,
      (∀ k ∈ ε.1, ∃ u ∈ e, u ∈ Z k) ∧ (∀ u ∈ e, ∃ k ∈ ε.1, u ∈ Z k) ∧
      (∀ k ∈ ε.1, ∃ u ∈ e, ∃ k2 ∈ ε.1, k2 ≠ k ∧ u ∈ Z k2) := by
    intro ε
    obtain ⟨⟨i, j⟩, hq⟩ : ∃ q : Fin h × Fin h, ε.1 = s(q.1, q.2) :=
      ⟨Quot.out ε.1, (Quot.out_eq _).symm⟩
    simp only at hq
    have hadj : (⊤ : SimpleGraph (Fin h)).Adj i j := by
      have := ε.2
      rw [hq] at this
      exact this
    have hne : i ≠ j := hadj.ne
    obtain ⟨x, hx, y, hy, hxy⟩ := M2.adj _ _ hadj
    refine ⟨s(x.1, y.1), hxy.2, ?_, ?_, ?_⟩
    · intro k hk
      rw [hq, Sym2.mem_iff] at hk
      rcases hk with rfl | rfl
      · exact ⟨x.1, Sym2.mem_mk_left _ _, x, hx, rfl⟩
      · exact ⟨y.1, Sym2.mem_mk_right _ _, y, hy, rfl⟩
    · intro u hu
      rw [Sym2.mem_iff] at hu
      rcases hu with rfl | rfl
      · exact ⟨i, by rw [hq]; exact Sym2.mem_mk_left _ _, x, hx, rfl⟩
      · exact ⟨j, by rw [hq]; exact Sym2.mem_mk_right _ _, y, hy, rfl⟩
    · intro k hk
      rw [hq, Sym2.mem_iff] at hk
      rcases hk with rfl | rfl
      · exact ⟨y.1, Sym2.mem_mk_right _ _, j, by rw [hq]; exact Sym2.mem_mk_right _ _,
          hne.symm, y, hy, rfl⟩
      · exact ⟨x.1, Sym2.mem_mk_left _ _, i, by rw [hq]; exact Sym2.mem_mk_left _ _,
          hne, x, hx, rfl⟩
  choose ee heeJ hee1 hee2 hee3 using hch
  -- the branch sets
  set ST : Fin h → Set (Sym2 V) := fun k => {f | ∃ v ∈ Z k, s(c k, v) ∈ J ∧ f = s(c k, v)} with hST
  set B : Fin h → Set V := fun k =>
    {y | (∃ v ∈ Z k, y ∈ Bl G v (d - 2)) ∨ ∃ f ∈ ST k, y ∈ Mv G d f} with hBdef
  have hSTp : ∀ k, ∀ f ∈ ST k, f ∈ J ∧ (∀ u ∈ f, u ∈ Z k) ∧ c k ∈ f := by
    rintro k f ⟨v, hv, hJv, rfl⟩
    refine ⟨hJv, fun u hu => ?_, Sym2.mem_mk_left _ _⟩
    rcases Sym2.mem_iff.mp hu with rfl | rfl
    · exact hcZ k
    · exact hv
  have hMP := fun e (he : e ∈ J) => Mv_props d hd (A : Set V) hA e (hJE e he)
  -- far lemmas
  have pf_bb : ∀ i j, i ≠ j → ∀ u ∈ Z i, ∀ w ∈ Z j,
      Far G (Bl G u (d - 2)) (Bl G w (d - 2)) := by
    intro i j hij u hu w hw
    have hne : u ≠ w := fun h => hZd i j hij u hu (h ▸ hw)
    have h1 := ge_succ (hA u (hZA i u hu) w (hZA j w hw) hne)
    exact far_of_balls (a := u) (b := w) (r := d - 2) (s := d - 2) (fun x hx => hx)
      (fun x hx => hx) (le_trans (by exact_mod_cast (by omega : d - 2 + (d - 2) + 2 ≤ 2 * d + 1)) h1)
  have pf_bm : ∀ f ∈ J, ∀ u ∈ (A : Set V), u ∉ f → Far G (Bl G u (d - 2)) (Mv G d f) :=
    fun f hf u hu hnot => (hMP f hf).2.1 u hu hnot
  have hnef : ∀ k, ∀ f ∈ ST k, ∀ i, i ≠ k → ∀ u ∈ Z i, u ∉ f := by
    intro k f hf i hik u hu huf
    exact hZd i k hik u hu ((hSTp k f hf).2.1 u huf)
  -- (1) radius
  have hPr : ∀ k, RadiusLE G (B k) (3 * d) := by
    intro k
    have hballin : ∀ v ∈ Z k, ∀ w, G.edist w v ≤ ((d - 2 : ℕ) : ℕ∞) → w ∈ B k :=
      fun v hv w hw => Or.inl ⟨v, hv, hw⟩
    have hSbin : ∀ f ∈ ST k, Sb G (d - 2) f ∪ Mv G d f ⊆ B k := by
      intro f hf y hy
      rcases hy with ⟨w, hw, hyw⟩ | hy
      · exact hballin w ((hSTp k f hf).2.1 w hw) y hyw
      · exact Or.inr ⟨f, hf, hy⟩
    have hballreach : ∀ v ∈ Z k, ∀ y, G.edist y v ≤ ((d - 2 : ℕ) : ℕ∞) → Reach G (B k) v y (d - 2) := by
      intro v hv y hy
      refine reach_ball (fun w hw => hballin v hv w hw) ?_
      rw [SimpleGraph.edist_comm]; exact hy
    have hc0 : c k ∈ B k := hballin (c k) (hcZ k) (c k) (by simp)
    refine reach_radius hc0 ?_
    intro y hy
    rcases hy with ⟨v, hv, hyv⟩ | ⟨f, hf, hyf⟩
    · rcases hcJ k v hv with rfl | hJv
      · exact (hballreach _ hv y hyv).mono_n (by omega)
      · have hf : s(c k, v) ∈ ST k := ⟨v, hv, hJv, rfl⟩
        have hne : c k ≠ v := isEdg_ne (hJE _ hJv)
        have h1 := ((hMP _ hJv).2.2.2.1 (c k) (Sym2.mem_mk_left _ _) v (Sym2.mem_mk_right _ _) hne)
        have h2 := h1.mono_set (hSbin _ hf)
        exact (h2.trans (hballreach v hv y hyv)).mono_n (by omega)
    · exact (((hMP f (hSTp k f hf).1).2.2.2.2.1 (c k) (hSTp k f hf).2.2 y hyf).mono_set
        (hSbin f hf)).mono_n (by omega)
  -- Far between branch sets
  have hPP : ∀ i j, i ≠ j → Far G (B i) (B j) := by
    intro i j hij y hy w hw
    rcases hy with ⟨u, hu, hy⟩ | ⟨f, hf, hy⟩ <;> rcases hw with ⟨u', hu', hw⟩ | ⟨f', hf', hw⟩
    · exact pf_bb i j hij u hu u' hu' y hy w hw
    · exact pf_bm f' (hSTp j f' hf').1 u (hZA i u hu) (hnef j f' hf' i hij u hu) y hy w hw
    · exact (pf_bm f (hSTp i f hf).1 u' (hZA j u' hu') (hnef i f hf j hij.symm u' hu')).symm y hy w hw
    · have hne : f ≠ f' := by
        intro h
        subst h
        exact hZd i j hij (c i) (hcZ i) ((hSTp j f hf').2.1 _ (hSTp i f hf).2.2)
      exact hJind f (hSTp i f hf).1 f' (hSTp j f' hf').1 hne y hy w hw
  have hQQ : ∀ ε ε' : (⊤ : SimpleGraph (Fin h)).edgeSet, ε ≠ ε' →
      Far G (Mv G d (ee ε)) (Mv G d (ee ε')) := by
    intro ε ε' hne
    refine hJind _ (heeJ ε) _ (heeJ ε') ?_
    intro heq
    apply hne
    apply Subtype.ext
    apply Sym2.ext
    have key : ∀ (ε ε' : (⊤ : SimpleGraph (Fin h)).edgeSet), ee ε = ee ε' →
        ∀ k ∈ ε.1, k ∈ ε'.1 := by
      intro ε ε' heq k hk
      obtain ⟨u, hu, hZu⟩ := hee1 ε k hk
      obtain ⟨k', hk', hZ'⟩ := hee2 ε' u (heq ▸ hu)
      have : k = k' := by
        by_contra hne
        exact hZd k k' hne u hZu hZ'
      exact this ▸ hk'
    intro k
    exact ⟨key ε ε' heq k, key ε' ε heq.symm k⟩
  have hfar : ∀ k (ε : (⊤ : SimpleGraph (Fin h)).edgeSet), k ∉ ε.1 →
      Far G (B k) (Mv G d (ee ε)) := by
    intro k ε hk y hy w hw
    rcases hy with ⟨u, hu, hy⟩ | ⟨f, hf, hy⟩
    · have hnot : u ∉ ee ε := by
        intro hue
        obtain ⟨k', hk', hZ'⟩ := hee2 ε u hue
        exact hZd k' k (fun h => hk (h ▸ hk')) u hZ' hu
      exact pf_bm _ (heeJ ε) u (hZA k u hu) hnot y hy w hw
    · have hne : f ≠ ee ε := by
        intro h
        have : c k ∈ ee ε := h ▸ (hSTp k f hf).2.2
        obtain ⟨k', hk', hZ'⟩ := hee2 ε _ this
        exact hZd k' k (fun h => hk (h ▸ hk')) _ hZ' (hcZ k)
      exact hJind f (hSTp k f hf).1 _ (heeJ ε) hne y hy w hw
  have hadj : ∀ k (ε : (⊤ : SimpleGraph (Fin h)).edgeSet), k ∈ ε.1 →
      Disjoint (B k) (Mv G d (ee ε)) ∧ ∃ x ∈ B k, ∃ y ∈ Mv G d (ee ε), G.Adj x y := by
    intro k ε hk
    obtain ⟨u1, hu1, hZ1⟩ := hee1 ε k hk
    obtain ⟨u2, hu2, k2, hk2, hk2ne, hZ2⟩ := hee3 ε k hk
    refine ⟨?_, ?_⟩
    · rw [Set.disjoint_left]
      intro y hy hy'
      rcases hy with ⟨u, hu, hy⟩ | ⟨f, hf, hy⟩
      · by_cases hue : u ∈ ee ε
        · exact Set.disjoint_left.mp ((hMP _ (heeJ ε)).2.2.1 u hue).1 hy hy'
        · exact (pf_bm _ (heeJ ε) u (hZA k u hu) hue).disjoint |> fun h => Set.disjoint_left.mp h hy hy'
      · have hne : f ≠ ee ε := by
          intro h
          have : u2 ∈ f := h ▸ hu2
          exact hZd k2 k hk2ne u2 hZ2 ((hSTp k f hf).2.1 _ this)
        exact Set.disjoint_left.mp (hJind f (hSTp k f hf).1 _ (heeJ ε) hne).disjoint hy hy'
    · obtain ⟨p, hp, q, hq, hpq⟩ := ((hMP _ (heeJ ε)).2.2.1 u1 hu1).2
      exact ⟨p, Or.inl ⟨u1, hZ1, hp⟩, q, hq, hpq⟩
  exact mkModel (⊤ : SimpleGraph (Fin h)) G (3 * d) 2 B (fun ε => Mv G d (ee ε)) hPr
    (fun ε => (hMP _ (heeJ ε)).1) hPP hQQ hfar hadj

end Compose

end FatFlat.Dev.L41
end

section
set_option autoImplicit false

namespace FatFlat.Dev.L41
open FatFlat.Hereditary FatFlat.Dev.L42

section Count
variable {V : Type}

/-- the graph on `A` joining distinct vertices at distance at most `2d+2` -/
def HA (G : SimpleGraph V) (d : ℕ) (A : Finset V) : SimpleGraph ↥A where
  Adj a b := a ≠ b ∧ G.edist (a : V) (b : V) ≤ ((2 * d + 2 : ℕ) : ℕ∞)
  symm := ⟨fun a b ⟨h, hj⟩ => ⟨h.symm, by rwa [SimpleGraph.edist_comm]⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

variable {G : SimpleGraph V}

open Classical in
lemma edge_count (d : ℕ) (A : Finset V) (s : ℝ) (hs : 0 < s) (hs10 : s ^ 10 = A.card)
    (hs2 : 2 ≤ s)
    (hno : ∀ B : Finset V, B ⊆ A → IsScattered G (2 * (d + 1)) (B : Set V) → (B.card : ℝ) < s) :
    s ^ 19 / 16 < (((HA G d A).edgeFinset.card : ℕ) : ℝ) := by
  classical
  set H0 := HA G d A with hH0
  set Δ0 : ℝ := s ^ 9 / 2 - 1 with hΔ0
  have hs9 : 512 ≤ s ^ 9 := by
    calc (512 : ℝ) = 2 ^ 9 := by norm_num
      _ ≤ s ^ 9 := pow_le_pow_left₀ (by norm_num) hs2 9
  have hΔpos : 0 < Δ0 := by rw [hΔ0]; linarith
  set T : Finset ↥A := Finset.univ.filter (fun v : ↥A => (H0.degree v : ℝ) ≤ Δ0) with hT
  have hdeg : ∀ v ∈ T, ((T.filter (H0.Adj v)).card : ℝ) ≤ Δ0 := by
    intro v hv
    have hv' : (H0.degree v : ℝ) ≤ Δ0 := by simpa [hT] using hv
    refine le_trans ?_ hv'
    have : (T.filter (H0.Adj v)).card ≤ H0.degree v := by
      rw [← H0.card_neighborFinset_eq_degree]
      refine Finset.card_le_card (fun w hw => ?_)
      simp only [Finset.mem_filter] at hw
      simpa using hw.2
    exact_mod_cast this
  obtain ⟨I, hIT, hIind, hIcard⟩ := greedy H0.Adj (fun a b h => h.symm) Δ0 T hdeg
  have hB : ((I.map ⟨Subtype.val, Subtype.val_injective⟩ : Finset V).card : ℝ) < s := by
    refine hno _ ?_ ?_
    · intro x hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hx
      exact a.2
    · intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hy)
      have hab : a ≠ b := fun h => hxy (by simp [h])
      have := hIind a ha b hb hab
      simp only [hH0, HA, not_and, not_le] at this
      have h2 := this hab
      show (((2 * (d + 1) : ℕ)) : ℕ∞) < _
      simpa [Nat.mul_add, mul_add] using h2
  rw [Finset.card_map] at hB
  have hTcard : (T.card : ℝ) < A.card / 2 := by
    have h1 : (T.card : ℝ) ≤ I.card * (Δ0 + 1) := hIcard
    have h2 : (I.card : ℝ) * (Δ0 + 1) < s * (Δ0 + 1) :=
      mul_lt_mul_of_pos_right hB (by rw [hΔ0]; linarith)
    have h3 : s * (Δ0 + 1) = A.card / 2 := by
      rw [← hs10, hΔ0]; ring
    linarith
  have hsum := H0.sum_degrees_eq_twice_card_edges
  have hsumR : ((∑ v, H0.degree v : ℕ) : ℝ) = 2 * ((H0.edgeFinset.card : ℕ) : ℝ) := by
    rw [hsum]; push_cast; ring
  have hcard : ((Finset.univ \ T).card : ℝ) + T.card = A.card := by
    have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
    have h2 : (Finset.univ : Finset ↥A).card = A.card := by simp
    rw [h2] at this
    exact_mod_cast this
  have hhigh : ((Finset.univ \ T).card : ℝ) * Δ0 ≤ ∑ v ∈ Finset.univ \ T, (H0.degree v : ℝ) := by
    have : ∑ v ∈ Finset.univ \ T, Δ0 ≤ ∑ v ∈ Finset.univ \ T, (H0.degree v : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      simp only [hT, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hv
      exact hv.le
    simpa using this
  have hall : ∑ v ∈ Finset.univ \ T, (H0.degree v : ℝ) ≤ ∑ v, (H0.degree v : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
  have hallR : ∑ v, (H0.degree v : ℝ) = 2 * ((H0.edgeFinset.card : ℕ) : ℝ) := by
    rw [← hsumR]; push_cast; rfl
  set E : ℝ := ((H0.edgeFinset.card : ℕ) : ℝ) with hE
  have hn : (A.card : ℝ) = s ^ 10 := hs10.symm
  have h1 : ((Finset.univ \ T).card : ℝ) > s ^ 10 / 2 := by linarith
  have h2 : 2 * E ≥ ((Finset.univ \ T).card : ℝ) * Δ0 := by linarith
  have h3 : ((Finset.univ \ T).card : ℝ) * Δ0 > s ^ 10 / 2 * Δ0 :=
    mul_lt_mul_of_pos_right h1 hΔpos
  have h4 : s ^ 19 = s ^ 10 * s ^ 9 := by ring
  have h5 : 0 < s ^ 10 := by positivity
  rw [hΔ0] at h3
  nlinarith [mul_le_mul_of_nonneg_left (by linarith : (4 : ℝ) ≤ s ^ 9) h5.le]

end Count

end FatFlat.Dev.L41
end

section
set_option autoImplicit false

namespace FatFlat.Dev.L41
open FatFlat.Hereditary FatFlat.Dev.L42

section Indep
variable {V : Type} {G : SimpleGraph V}

lemma edist_chain4 (a b c d e : V) :
    G.edist a e ≤ G.edist a b + G.edist b c + G.edist c d + G.edist d e := by
  calc G.edist a e ≤ G.edist a d + G.edist d e := SimpleGraph.edist_triangle
    _ ≤ (G.edist a c + G.edist c d) + G.edist d e := by
        gcongr; exact SimpleGraph.edist_triangle
    _ ≤ ((G.edist a b + G.edist b c) + G.edist c d) + G.edist d e := by
        gcongr; exact SimpleGraph.edist_triangle

lemma le_one_of_lt_two {x : ℕ∞} (h : x < 2) : x ≤ 1 := by
  obtain ⟨k, hk, -⟩ := enat_nat _ 2 h.le
  rw [hk] at h ⊢
  have : k < 2 := by exact_mod_cast h
  exact_mod_cast (by omega : k ≤ 1)

open Classical in
lemma hEdg_of_mem (d : ℕ) (A : Finset V) (e : Sym2 ↥A) (he : e ∈ (HA G d A).edgeFinset) :
    IsEdg G d (A : Set V) (e.map Subtype.val) := by
  classical
  induction e using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact ⟨a.1, a.2, b.1, b.2, fun h => he.1 (Subtype.ext h), he.2, by simp [Sym2.map_pair_eq]⟩

open Classical in
lemma indep_count (d : ℕ) (hd : 2 ≤ d) (A : Finset V) (s : ℝ)
    (hA : ∀ a ∈ (A : Set V), ∀ b ∈ (A : Set V), a ≠ b → ((2 * d : ℕ) : ℕ∞) < G.edist a b)
    (hno1 : ∀ v : V, (((A : Set V) ∩ ball G {v} (d + 6)).ncard : ℝ) < s) :
    ∃ J0 : Finset (Sym2 ↥A), J0 ⊆ (HA G d A).edgeFinset ∧
      (∀ e ∈ J0, ∀ f ∈ J0, e ≠ f →
        Far G (Mv G d (e.map Subtype.val)) (Mv G d (f.map Subtype.val))) ∧
      (((HA G d A).edgeFinset.card : ℕ) : ℝ) ≤ J0.card * (s ^ 2 / 2) := by
  set E := (HA G d A).edgeFinset with hE
  set R : Sym2 ↥A → Sym2 ↥A → Prop := fun e f =>
    e ≠ f ∧ ¬ Far G (Mv G d (e.map Subtype.val)) (Mv G d (f.map Subtype.val)) with hR
  have hRsymm : ∀ a b, R a b → R b a := fun a b ⟨h1, h2⟩ => ⟨h1.symm, fun h => h2 h.symm⟩
  have hdeg : ∀ e ∈ E, ((E.filter (R e)).card : ℝ) ≤ s ^ 2 / 2 - 1 := by
    intro e he
    obtain ⟨m, hm1, hm2⟩ := (Mv_props d hd (A : Set V) hA _ (hEdg_of_mem d A e he)).2.2.2.2.2
    set Bs : Finset V := A.filter (fun u => G.edist u m ≤ ((d + 6 : ℕ) : ℕ∞)) with hBs
    have hBcard : (Bs.card : ℝ) < s := by
      have : (((A : Set V) ∩ ball G {m} (d + 6)).ncard) = Bs.card := by
        rw [← Set.ncard_coe_finset]
        congr 1
        ext u
        simp [hBs, ball]
      rw [← this]; exact hno1 m
    have hsub : (insert e (E.filter (R e))).image (Sym2.map (Subtype.val : ↥A → V)) ⊆
        Bs.offDiag.image Sym2.mk.uncurry := by
      intro g hg
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
      have hfE : f ∈ E := by
        rcases Finset.mem_insert.mp hf with rfl | hf
        · exact he
        · exact (Finset.mem_filter.mp hf).1
      obtain ⟨mf, hmf1, hmf2⟩ := (Mv_props d hd (A : Set V) hA _ (hEdg_of_mem d A f hfE)).2.2.2.2.2
      have hbound : ∀ u ∈ f.map Subtype.val, G.edist u m ≤ ((d + 6 : ℕ) : ℕ∞) := by
        intro u hu
        rcases Finset.mem_insert.mp hf with rfl | hf'
        · exact (hm2 u hu).trans (by exact_mod_cast (by omega : d + 1 ≤ d + 6))
        · have hRf := (Finset.mem_filter.mp hf').2
          have hnf : ¬ Far G (Mv G d (e.map Subtype.val)) (Mv G d (f.map Subtype.val)) := hRf.2
          unfold Far at hnf
          push_neg at hnf
          obtain ⟨p, hp, q, hq, hpq⟩ := hnf
          have h1 := le_one_of_lt_two hpq
          have := edist_chain4 (G := G) u mf q p m
          calc G.edist u m ≤ G.edist u mf + G.edist mf q + G.edist q p + G.edist p m := this
            _ ≤ ((d + 1 : ℕ) : ℕ∞) + ((2 : ℕ) : ℕ∞) + ((1 : ℕ) : ℕ∞) + ((2 : ℕ) : ℕ∞) := by
                gcongr
                · exact hmf2 u hu
                · rw [SimpleGraph.edist_comm]; exact hmf1 q hq
                · rw [SimpleGraph.edist_comm]; exact h1
                · exact hm1 p hp
            _ = ((d + 6 : ℕ) : ℕ∞) := by norm_cast
      induction f using Sym2.ind with
      | _ a b =>
        have hadj := hfE
        rw [hE, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hadj
        refine Finset.mem_image.mpr ⟨(a.1, b.1), ?_, by simp [Sym2.map_pair_eq]⟩
        rw [Finset.mem_offDiag]
        refine ⟨?_, ?_, fun h => hadj.1 (Subtype.ext h)⟩
        · exact Finset.mem_filter.mpr ⟨a.2, hbound a.1 (by simp [Sym2.map_pair_eq])⟩
        · exact Finset.mem_filter.mpr ⟨b.2, hbound b.1 (by simp [Sym2.map_pair_eq])⟩
    have hinj : Function.Injective (Sym2.map (Subtype.val : ↥A → V)) :=
      Sym2.map.injective Subtype.val_injective
    have hcard1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj, Sym2.card_image_offDiag] at hcard1
    have henot : e ∉ E.filter (R e) := fun h => (Finset.mem_filter.mp h).2.1 rfl
    rw [Finset.card_insert_of_notMem henot] at hcard1
    have h2 : (((E.filter (R e)).card + 1 : ℕ) : ℝ) ≤ ((Bs.card.choose 2 : ℕ) : ℝ) := by
      exact_mod_cast hcard1
    rw [Nat.cast_choose_two] at h2
    push_cast at h2
    have hb0 : (0 : ℝ) ≤ Bs.card := by positivity
    nlinarith
  obtain ⟨I, hIE, hIind, hIcard⟩ := greedy R hRsymm (s ^ 2 / 2 - 1) E hdeg
  refine ⟨I, hIE, ?_, by linarith⟩
  intro e he f hf hef
  by_contra hnf
  exact hIind e he f hf hef ⟨hef, hnf⟩

end Indep

end FatFlat.Dev.L41
end

section
set_option autoImplicit false

namespace FatFlat.Dev.L41
open FatFlat.Hereditary FatFlat.Dev.L42

section Final
variable {V : Type} {G : SimpleGraph V}

open Classical in
lemma edgeSet_HJ (d : ℕ) (A : Finset V) (J0 : Finset (Sym2 ↥A))
    (hJ0 : J0 ⊆ (HA G d A).edgeFinset) :
    (HJ (↑(J0.image (Sym2.map (Subtype.val : ↥A → V))) : Set (Sym2 V)) A).edgeSet = ↑J0 := by
  have hinj : Function.Injective (Sym2.map (Subtype.val : ↥A → V)) :=
    Sym2.map.injective Subtype.val_injective
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.mem_edgeSet, HJ_adj]
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Sym2.map_mk]
    constructor
    · rintro ⟨hne, e0, he0, heq⟩
      have : e0 = s(a, b) := hinj (by simpa [Sym2.map_mk] using heq)
      rw [← this]; exact he0
    · intro h
      have := hJ0 h
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
      exact ⟨this.1, s(a, b), h, by simp [Sym2.map_mk]⟩

end Final

end FatFlat.Dev.L41

namespace FatFlat.Hereditary
open FatFlat.Dev.L41 FatFlat.Dev.L42 in
theorem chk_lemma_4_1 (h d : ℕ) (hh : 0 < h) (hd : 2 ≤ d) (V : Type) [Fintype V]
    (G : SimpleGraph V) (A : Finset V) (hA : IsScattered G (2 * d) (A : Set V))
    (hAcard : 4 ^ 5 * (h + 1) ^ 10 ≤ A.card) :
    (∃ v : V, (A.card : ℝ) ^ ((1 : ℝ) / 10) ≤ (((A : Set V) ∩ ball G {v} (d + 6)).ncard : ℝ)) ∨
    (∃ B : Finset V, B ⊆ A ∧ (A.card : ℝ) ^ ((1 : ℝ) / 10) ≤ (B.card : ℝ) ∧
      IsScattered G (2 * (d + 1)) (B : Set V)) ∨
    IsShallowInducedMinorOneSubdiv (⊤ : SimpleGraph (Fin h)) G (3 * d) 2 := by
  classical
  by_cases h1 : ∃ v : V, (A.card : ℝ) ^ ((1 : ℝ) / 10) ≤ (((A : Set V) ∩ ball G {v} (d + 6)).ncard : ℝ)
  · exact Or.inl h1
  by_cases h2 : ∃ B : Finset V, B ⊆ A ∧ (A.card : ℝ) ^ ((1 : ℝ) / 10) ≤ (B.card : ℝ) ∧
      IsScattered G (2 * (d + 1)) (B : Set V)
  · exact Or.inr (Or.inl h2)
  right; right
  set s : ℝ := (A.card : ℝ) ^ ((1 : ℝ) / 10) with hsdef
  have hn : (0 : ℝ) < A.card := by
    have : 0 < A.card := lt_of_lt_of_le (by positivity) hAcard
    exact_mod_cast this
  have hs : 0 < s := Real.rpow_pos_of_pos hn _
  have hpow : ∀ k : ℕ, s ^ k = (A.card : ℝ) ^ ((k : ℝ) / 10) := by
    intro k
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    congr 1; ring
  have hs10 : s ^ 10 = A.card := by
    rw [hpow]; norm_num
  have hs15 : s ^ 15 = (A.card : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [hpow]; norm_num
  have hsge : 2 * ((h : ℝ) + 1) ≤ s := by
    by_contra hlt
    rw [not_le] at hlt
    have h3 := pow_lt_pow_left₀ hlt hs.le (by norm_num : (10 : ℕ) ≠ 0)
    rw [hs10] at h3
    have h4 : ((4 ^ 5 * (h + 1) ^ 10 : ℕ) : ℝ) ≤ A.card := by exact_mod_cast hAcard
    push_cast at h4
    have : (2 * ((h : ℝ) + 1)) ^ 10 = 4 ^ 5 * ((h : ℝ) + 1) ^ 10 := by ring
    linarith
  have hs2 : 2 ≤ s := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  have hno1 : ∀ v : V, (((A : Set V) ∩ ball G {v} (d + 6)).ncard : ℝ) < s := fun v =>
    not_le.mp (fun hle => h1 ⟨v, hle⟩)
  have hno2 : ∀ B : Finset V, B ⊆ A → IsScattered G (2 * (d + 1)) (B : Set V) →
      (B.card : ℝ) < s := fun B hB hsc => not_le.mp (fun hle => h2 ⟨B, hB, hle, hsc⟩)
  have hEc := edge_count d A s hs hs10 hs2 hno2
  obtain ⟨J0, hJ0E, hJ0ind, hJ0card⟩ := indep_count d hd A s hA hno1
  have hinj : Function.Injective (Sym2.map (Subtype.val : ↥A → V)) :=
    Sym2.map.injective Subtype.val_injective
  set J : Set (Sym2 V) := ↑(J0.image (Sym2.map (Subtype.val : ↥A → V))) with hJ
  have hJE : ∀ e ∈ J, IsEdg G d (A : Set V) e := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp he)
    exact hEdg_of_mem d A e0 (hJ0E he0)
  have hJind : ∀ e ∈ J, ∀ f ∈ J, e ≠ f → Far G (Mv G d e) (Mv G d f) := by
    intro e he f hf hef
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp he)
    obtain ⟨f0, hf0, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hf)
    exact hJ0ind e0 he0 f0 hf0 (fun h => hef (by rw [h]))
  have hedge : (HJ J A).edgeSet = ↑J0 := edgeSet_HJ d A J0 hJ0E
  have hcardV : Fintype.card ↥A = A.card := Fintype.card_coe A
  have hJcard : s ^ 17 / 8 < J0.card := by
    by_contra hle
    rw [not_lt] at hle
    have h5 : (J0.card : ℝ) * (s ^ 2 / 2) ≤ s ^ 17 / 8 * (s ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hle (by positivity)
    have : s ^ 17 / 8 * (s ^ 2 / 2) = s ^ 19 / 16 := by ring
    linarith
  have hE : (((h + 1).choose 2 : ℕ) : ℝ) * (A.card : ℝ) ^ ((3 : ℝ) / 2) <
      (((HJ J A).edgeSet.ncard : ℕ) : ℝ) := by
    rw [hedge, Set.ncard_coe_finset, ← hs15, Nat.cast_choose_two]
    push_cast
    have hs15p : 0 < s ^ 15 := by positivity
    have hq : 4 * ((h : ℝ) + 1) ^ 2 ≤ s ^ 2 := by nlinarith
    have hh1 : (0 : ℝ) < h := by exact_mod_cast hh
    have h6 : ((h : ℝ) + 1) * ((h : ℝ) + 1 - 1) / 2 * s ^ 15 < s ^ 17 / 8 := by
      have : ((h : ℝ) + 1) * ((h : ℝ) + 1 - 1) / 2 < ((h : ℝ) + 1) ^ 2 / 2 := by nlinarith
      calc ((h : ℝ) + 1) * ((h : ℝ) + 1 - 1) / 2 * s ^ 15 < ((h : ℝ) + 1) ^ 2 / 2 * s ^ 15 :=
            mul_lt_mul_of_pos_right this hs15p
        _ ≤ s ^ 2 / 8 * s ^ 15 := by
            apply mul_le_mul_of_nonneg_right _ hs15p.le
            linarith
        _ = s ^ 17 / 8 := by ring
    linarith
  have hmin := FatFlat.Hereditary.theorem_2_1 h A.card hh (by exact_mod_cast hn) ↥A hcardV (HJ J A) hE
  exact compose d h hd A hA J hJE hJind hmin

end FatFlat.Hereditary
end

theorem solution : type_of% @FatFlat.Hereditary.chk_lemma_4_1 := @FatFlat.Hereditary.chk_lemma_4_1
