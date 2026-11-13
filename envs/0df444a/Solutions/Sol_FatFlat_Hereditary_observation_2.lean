-- Prove2me | solution 1 for FatFlat.Hereditary.observation_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:33:29.378666+00:00
-- url     : https://prove2.me/submissions/8f631ab0-f150-4794-8186-a811f2b961fe

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Classes

section
set_option autoImplicit false

namespace FatFlat.Dev.Obs2
open FatFlat.Hereditary

abbrev KE (n : ℕ) := ↥(⊤ : SimpleGraph (Fin n)).edgeSet
abbrev KV (r n : ℕ) := Fin n ⊕ (Σ e : KE n, Fin (r - 1 + 1))

noncomputable def KG (r n : ℕ) : SimpleGraph (KV r n) := subdividedClique r n
noncomputable def WG (r n : ℕ) : SimpleGraph (KV r n) := web r n

lemma KG_le_WG (r n : ℕ) : KG r n ≤ WG r n := by
  intro x y h
  exact Or.inl h

noncomputable def e1 {n : ℕ} (e : KE n) : Fin n := (Quot.out (e : Sym2 (Fin n))).1
noncomputable def e2 {n : ℕ} (e : KE n) : Fin n := (Quot.out (e : Sym2 (Fin n))).2

lemma e_eq {n : ℕ} (e : KE n) : (e : Sym2 (Fin n)) = s(e1 e, e2 e) := by
  have h : (Quot.out (e : Sym2 (Fin n))) = (e1 e, e2 e) := rfl
  conv_lhs => rw [← Quot.out_eq (e : Sym2 (Fin n))]
  exact congrArg (Quot.mk _) h

lemma e12_ne {n : ℕ} (e : KE n) : e1 e ≠ e2 e := by
  intro h
  have := e.2
  rw [e_eq e, h] at this
  simp at this

lemma mem_iff {n : ℕ} (e : KE n) (u : Fin n) : u ∈ (e : Sym2 (Fin n)) ↔ u = e1 e ∨ u = e2 e := by
  rw [e_eq]; simp [Sym2.mem_iff]

/-! adjacency in K -/

lemma KG_adj_inl_inr {r n : ℕ} (v : Fin n) (e : KE n) (i : Fin (r - 1 + 1)) :
    (KG r n).Adj (Sum.inl v) (Sum.inr ⟨e, i⟩) ↔
      (v = e1 e ∧ i.val = 0) ∨ (v = e2 e ∧ i.val = r - 1) := by
  unfold KG subdividedClique SparseDisc.subdivide
  simp [SimpleGraph.fromRel_adj, e1, e2]

lemma KG_adj_inr_inr {r n : ℕ} (e e' : KE n) (i : Fin (r - 1 + 1)) (j : Fin (r - 1 + 1)) :
    (KG r n).Adj (Sum.inr ⟨e, i⟩) (Sum.inr ⟨e', j⟩) ↔
      e = e' ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  unfold KG subdividedClique SparseDisc.subdivide
  simp only [SimpleGraph.fromRel_adj, ne_eq, Sum.inr.injEq]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨h.1, Or.inl h.2⟩
    · exact ⟨h.1.symm, Or.inr h.2⟩
  · rintro ⟨rfl, h | h⟩
    · refine ⟨?_, Or.inl ⟨rfl, h⟩⟩
      intro h'
      have := Sigma.mk.inj h'
      simp at this
      omega
    · refine ⟨?_, Or.inr ⟨rfl, h⟩⟩
      intro h'
      have := Sigma.mk.inj h'
      simp at this
      omega

lemma KG_not_adj_inl_inl {r n : ℕ} (a b : Fin n) :
    ¬ (KG r n).Adj (Sum.inl a) (Sum.inl b) := by
  unfold KG subdividedClique SparseDisc.subdivide
  simp [SimpleGraph.fromRel_adj]

/-! web adjacency: K-adjacency or common principal neighbour -/

lemma WG_adj {r n : ℕ} (x y : KV r n) :
    (WG r n).Adj x y → (KG r n).Adj x y ∨
      ∃ s : Fin n, (KG r n).Adj (Sum.inl s) x ∧ (KG r n).Adj (Sum.inl s) y := by
  intro h
  unfold WG web webOf at h
  rcases h with h | h
  · exact Or.inl h
  · right
    rw [SimpleGraph.fromRel_adj] at h
    rcases h with ⟨_, ⟨p, ⟨s, rfl⟩, h1, h2⟩ | ⟨p, ⟨s, rfl⟩, h1, h2⟩⟩
    · exact ⟨s, h1, h2⟩
    · exact ⟨s, h2, h1⟩

/-! Lipschitz functions give lower bounds on distances -/

def Lip {V : Type} (G : SimpleGraph V) (f : V → ℕ) : Prop := ∀ x y, G.Adj x y → f x ≤ f y + 1

lemma Lip.walk {V : Type} {G : SimpleGraph V} {f : V → ℕ} (hf : Lip G f) :
    ∀ {x y : V} (w : G.Walk x y), f x ≤ f y + w.length := by
  intro x y w
  induction w with
  | nil => simp
  | cons h w ih =>
    have := hf _ _ h
    simp only [SimpleGraph.Walk.length_cons]
    omega

lemma Lip.edist_ge {V : Type} {G : SimpleGraph V} {f : V → ℕ} (hf : Lip G f) (x y : V) (c d : ℕ)
    (hx : f x ≤ c) (hy : c + d ≤ f y) : (d : ℕ∞) ≤ G.edist y x := by
  by_cases h : G.edist y x = ⊤
  · simp [h]
  · obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_ne_top h
    rw [← hw]
    have := hf.walk w
    have h3 : d ≤ w.length := by omega
    exact_mod_cast h3

end FatFlat.Dev.Obs2
end

section
set_option autoImplicit false

namespace FatFlat.Dev.Obs2
open FatFlat.Hereditary

/-- distance-like function from the principal `u`, capped at `r + 1`. -/
noncomputable def Dp (r : ℕ) {n : ℕ} (u : Fin n) : KV r n → ℕ
  | Sum.inl v => if v = u then 0 else r + 1
  | Sum.inr ⟨e, i⟩ => if u = e1 e then i.val + 1 else if u = e2 e then r - i.val else r + 1

lemma Dp_le {r n : ℕ} (u : Fin n) (x : KV r n) : Dp r u x ≤ r + 1 := by
  rcases x with v | ⟨e, i⟩
  · simp only [Dp]; split_ifs <;> omega
  · have := i.2
    simp only [Dp]; split_ifs <;> omega

lemma Dp_inr_pos {r n : ℕ} (hr : 3 ≤ r) (u : Fin n) (e : KE n) (i : Fin (r - 1 + 1)) :
    1 ≤ Dp r u (Sum.inr ⟨e, i⟩) := by
  have := i.2
  simp only [Dp]; split_ifs <;> omega

lemma Dp_adj {r n : ℕ} (hr : 3 ≤ r) (u : Fin n) (x y : KV r n) (h : (KG r n).Adj x y) :
    Dp r u x ≤ Dp r u y + 1 := by
  rcases x with a | ⟨e, i⟩ <;> rcases y with b | ⟨e', j⟩
  · exact absurd h (KG_not_adj_inl_inl a b)
  · rw [KG_adj_inl_inr] at h
    have := j.2
    have h12 := e12_ne e'
    simp only [Dp]
    rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> split_ifs <;> first | omega | grind
  · rw [SimpleGraph.adj_comm, KG_adj_inl_inr] at h
    have := i.2
    have h12 := e12_ne e
    simp only [Dp]
    rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> split_ifs <;> first | omega | grind
  · rw [KG_adj_inr_inr] at h
    obtain ⟨rfl, h⟩ := h
    have := i.2
    have := j.2
    have h12 := e12_ne e
    simp only [Dp]
    split_ifs <;> omega


lemma Dp_nbr {r n : ℕ} (hr : 3 ≤ r) (s : Fin n) (x : KV r n) (h : (KG r n).Adj (Sum.inl s) x) :
    Dp r s x = 1 := by
  rcases x with b | ⟨e, i⟩
  · exact absurd h (KG_not_adj_inl_inl s b)
  · rw [KG_adj_inl_inr] at h
    have h12 := e12_ne e
    simp only [Dp]
    rcases h with ⟨h, h'⟩ | ⟨h, h'⟩
    · rw [if_pos h]; omega
    · rw [if_neg (by intro h''; exact h12 (h''.symm.trans h)), if_pos h]; omega

lemma Dp_clique {r n : ℕ} (hr : 3 ≤ r) (u s : Fin n) (x y : KV r n)
    (hx : (KG r n).Adj (Sum.inl s) x) (hy : (KG r n).Adj (Sum.inl s) y) :
    Dp r u x ≤ Dp r u y + 1 := by
  by_cases hsu : s = u
  · subst hsu
    rw [Dp_nbr hr s x hx, Dp_nbr hr s y hy]
    omega
  · have h1 := Dp_adj hr u _ _ hy
    have h2 := Dp_le (r := r) u x
    have h3 : Dp r u (Sum.inl s) = r + 1 := by simp [Dp, hsu]
    omega

lemma Dp_lipW {r n : ℕ} (hr : 3 ≤ r) (u : Fin n) : Lip (WG r n) (Dp r u) := by
  intro x y h
  rcases WG_adj x y h with h | ⟨s, hx, hy⟩
  · exact Dp_adj hr u x y h
  · exact Dp_clique hr u s x y hx hy

lemma Lip.min {V : Type} {G : SimpleGraph V} {f g : V → ℕ} (hf : Lip G f) (hg : Lip G g) :
    Lip G (fun x => min (f x) (g x)) := by
  intro x y h
  have := hf x y h
  have := hg x y h
  simp only
  omega

noncomputable def Nf {r n : ℕ} (f : KE n) (x : KV r n) : ℕ := min (Dp r (e1 f) x) (Dp r (e2 f) x)

lemma Nf_lipK {r n : ℕ} (hr : 3 ≤ r) (f : KE n) : Lip (KG r n) (Nf (r := r) f) :=
  Lip.min (fun x y h => Dp_adj hr _ x y h) (fun x y h => Dp_adj hr _ x y h)

end FatFlat.Dev.Obs2
end

section
set_option autoImplicit false

namespace FatFlat.Dev.Obs2
open FatFlat.Hereditary

/-- potential for the edge `f`: signed-ish distance to the middle segment of the path of `f`. -/
noncomputable def Fe (r : ℕ) {n : ℕ} (a C : ℕ) (f : KE n) : KV r n → ℕ
  | Sum.inl z => min C (a + Nf f (Sum.inl z : KV r n) - 1)
  | Sum.inr ⟨g, i⟩ =>
      if g = f then a - min a (Nf f (Sum.inr ⟨g, i⟩ : KV r n))
      else min C (a + Nf f (Sum.inr ⟨g, i⟩ : KV r n) - 1)

lemma Nf_inl {r n : ℕ} (f : KE n) (s : Fin n) :
    Nf (r := r) f (Sum.inl s) = if s = e1 f ∨ s = e2 f then 0 else r + 1 := by
  simp only [Nf, Dp]
  split_ifs <;> first | omega | grind

lemma Nf_pos {r n : ℕ} (hr : 3 ≤ r) (f : KE n) (e : KE n) (i : Fin (r - 1 + 1)) :
    1 ≤ Nf (r := r) f (Sum.inr ⟨e, i⟩) := by
  have h1 := Dp_inr_pos hr (e1 f) e i
  have h2 := Dp_inr_pos hr (e2 f) e i
  simp only [Nf]; omega

lemma Fe_inl {r n : ℕ} (f : KE n) (a C : ℕ) (ha : 1 ≤ a) (haC : a ≤ C) (hC : C ≤ a + r - 1)
    (s : Fin n) :
    Fe r a C f (Sum.inl s) = if s = e1 f ∨ s = e2 f then a - 1 else C := by
  simp only [Fe, Nf_inl]
  split_ifs <;> omega

lemma Fe_nbr {r n : ℕ} (hr : 3 ≤ r) (f : KE n) (a C : ℕ) (ha : 1 ≤ a) (haC : a ≤ C)
    (hC : C ≤ a + r - 1) (s : Fin n) (x : KV r n) (h : (KG r n).Adj (Sum.inl s) x) :
    (s = e1 f ∨ s = e2 f → Fe r a C f x = a - 1 ∨ Fe r a C f x = a) ∧
    (¬ (s = e1 f ∨ s = e2 f) → Fe r a C f x = C) := by
  rcases x with b | ⟨g, i⟩
  · exact absurd h (KG_not_adj_inl_inl s b)
  · rw [KG_adj_inl_inr] at h
    have h12 := e12_ne g
    have hf12 := e12_ne f
    have hp := Nf_pos hr f g i
    have hi := i.2
    have hNle1 : (s = e1 f ∨ s = e2 f) → Nf (r := r) f (Sum.inr ⟨g, i⟩) ≤ 1 := by
      intro hs
      have := Dp_nbr hr s _ (by rw [KG_adj_inl_inr]; exact h)
      simp only [Nf]
      rcases hs with rfl | rfl <;> omega
    have hNge : ¬ (s = e1 f ∨ s = e2 f) → r ≤ Nf (r := r) f (Sum.inr ⟨g, i⟩) := by
      intro hs
      have h1 := Dp_adj hr (e1 f) _ _ (show (KG r n).Adj (Sum.inl s) (Sum.inr ⟨g, i⟩) by
        rw [KG_adj_inl_inr]; exact h)
      have h2 := Dp_adj hr (e2 f) _ _ (show (KG r n).Adj (Sum.inl s) (Sum.inr ⟨g, i⟩) by
        rw [KG_adj_inl_inr]; exact h)
      have h3 : Dp r (e1 f) (Sum.inl s) = r + 1 := by
        simp only [Dp]; rw [if_neg]; intro h'; exact hs (Or.inl h')
      have h4 : Dp r (e2 f) (Sum.inl s) = r + 1 := by
        simp only [Dp]; rw [if_neg]; intro h'; exact hs (Or.inr h')
      simp only [Nf]; omega
    constructor
    · intro hs
      have := hNle1 hs
      simp only [Fe]
      split_ifs <;> omega
    · intro hs
      have := hNge hs
      have hgf : g ≠ f := by
        rintro rfl
        apply hs
        rcases h with ⟨h, _⟩ | ⟨h, _⟩
        · exact Or.inl h
        · exact Or.inr h
      simp only [Fe]
      rw [if_neg hgf]
      omega


lemma Fe_adj_inl {r n : ℕ} (hr : 3 ≤ r) (f : KE n) (a C : ℕ) (ha : 1 ≤ a) (haC : a ≤ C)
    (hC : C ≤ a + r - 1) (s : Fin n) (x : KV r n) (h : (KG r n).Adj (Sum.inl s) x) :
    Fe r a C f (Sum.inl s) ≤ Fe r a C f x + 1 ∧ Fe r a C f x ≤ Fe r a C f (Sum.inl s) + 1 := by
  have h1 := Fe_nbr hr f a C ha haC hC s x h
  rw [Fe_inl f a C ha haC hC]
  by_cases hs : s = e1 f ∨ s = e2 f
  · have := h1.1 hs
    rw [if_pos hs]; omega
  · have := h1.2 hs
    rw [if_neg hs]; omega

lemma Fe_lipK {r n : ℕ} (hr : 3 ≤ r) (f : KE n) (a C : ℕ) (ha : 1 ≤ a) (haC : a ≤ C)
    (hC : C ≤ a + r - 1) : Lip (KG r n) (Fe r a C f) := by
  intro x y h
  rcases x with u | ⟨g, i⟩ <;> rcases y with v | ⟨g', j⟩
  · exact absurd h (KG_not_adj_inl_inl u v)
  · exact (Fe_adj_inl hr f a C ha haC hC u _ h).1
  · exact (Fe_adj_inl hr f a C ha haC hC v _ h.symm).2
  · rw [KG_adj_inr_inr] at h
    obtain ⟨rfl, h⟩ := h
    have hl := Nf_lipK hr f (Sum.inr ⟨g, i⟩) (Sum.inr ⟨g, j⟩)
      (by rw [KG_adj_inr_inr]; exact ⟨rfl, h⟩)
    have hl2 := Nf_lipK hr f (Sum.inr ⟨g, j⟩) (Sum.inr ⟨g, i⟩)
      (by rw [KG_adj_inr_inr]; exact ⟨rfl, by omega⟩)
    simp only [Fe]
    split_ifs <;> omega

lemma Fe_lipW {r n : ℕ} (hr : 3 ≤ r) (f : KE n) (a C : ℕ) (ha : 1 ≤ a) (haC : a ≤ C)
    (hC : C ≤ a + r - 1) : Lip (WG r n) (Fe r a C f) := by
  intro x y h
  rcases WG_adj x y h with h | ⟨s, hx, hy⟩
  · exact Fe_lipK hr f a C ha haC hC x y h
  · have h1 := Fe_nbr hr f a C ha haC hC s x hx
    have h2 := Fe_nbr hr f a C ha haC hC s y hy
    by_cases hs : s = e1 f ∨ s = e2 f
    · have := h1.1 hs
      have := h2.1 hs
      omega
    · have := h1.2 hs
      have := h2.2 hs
      omega

end FatFlat.Dev.Obs2
end

section
set_option autoImplicit false

namespace FatFlat.Dev.Obs2
open FatFlat.Hereditary

def VS (r a : ℕ) {n : ℕ} (u : Fin n) : Set (KV r n) := {x | Dp r u x ≤ a}

def ES (r a : ℕ) {n : ℕ} (f : KE n) : Set (KV r n) :=
  {x | ∃ i : Fin (r - 1 + 1), a ≤ i.val + 1 ∧ i.val + a ≤ r ∧ x = Sum.inr ⟨f, i⟩}

lemma edist_adj_le {V : Type} (G : SimpleGraph V) (S : Set V) (x y : V) (hx : x ∈ S) (hy : y ∈ S)
    (h : G.Adj x y) : (G.induce S).edist ⟨x, hx⟩ ⟨y, hy⟩ ≤ 1 := by
  rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
  exact Or.inl h

lemma Dp_pred {r n : ℕ} (hr : 3 ≤ r) (u : Fin n) (x : KV r n) (m : ℕ) (hm : m + 1 ≤ r)
    (hx : Dp r u x = m + 1) : ∃ y : KV r n, (KG r n).Adj x y ∧ Dp r u y = m := by
  rcases x with v | ⟨e, i⟩
  · simp only [Dp] at hx; split_ifs at hx <;> omega
  · have hi := i.2
    have h12 := e12_ne e
    simp only [Dp] at hx
    by_cases h1 : u = e1 e
    · rw [if_pos h1] at hx
      by_cases hm0 : m = 0
      · subst hm0
        refine ⟨Sum.inl (e1 e), ?_, ?_⟩
        · rw [SimpleGraph.adj_comm, KG_adj_inl_inr]; left; exact ⟨rfl, by omega⟩
        · simp [Dp, h1]
      · refine ⟨Sum.inr ⟨e, ⟨i.val - 1, by have := i.2; omega⟩⟩, ?_, ?_⟩
        · rw [KG_adj_inr_inr]; refine ⟨rfl, Or.inr ?_⟩; simp only; have := i.2; omega
        · simp only [Dp, if_pos h1]; omega
    · rw [if_neg h1] at hx
      by_cases h2 : u = e2 e
      · rw [if_pos h2] at hx
        by_cases hm0 : m = 0
        · subst hm0
          refine ⟨Sum.inl (e2 e), ?_, ?_⟩
          · rw [SimpleGraph.adj_comm, KG_adj_inl_inr]; right; exact ⟨rfl, by omega⟩
          · simp [Dp, h2]
        · refine ⟨Sum.inr ⟨e, ⟨i.val + 1, by have := i.2; have := hx; omega⟩⟩, ?_, ?_⟩
          · rw [KG_adj_inr_inr]; refine ⟨rfl, Or.inl ?_⟩; simp only
          · simp only [Dp, if_neg h1, if_pos h2]; omega
      · rw [if_neg h2] at hx; omega

lemma VS_radius {r n : ℕ} (hr : 3 ≤ r) (G : SimpleGraph (KV r n)) (hG : KG r n ≤ G) (a : ℕ)
    (ha : a ≤ r) (u : Fin n) : RadiusLE G (VS r a u) a := by
  have hu : (Sum.inl u : KV r n) ∈ VS r a u := by simp [VS, Dp]
  refine ⟨⟨Sum.inl u, hu⟩, ?_⟩
  have key : ∀ m : ℕ, ∀ x : KV r n, ∀ hx : x ∈ VS r a u, Dp r u x = m →
      (G.induce (VS r a u)).edist ⟨Sum.inl u, hu⟩ ⟨x, hx⟩ ≤ m := by
    intro m
    induction m with
    | zero =>
      intro x hx h0
      have : x = Sum.inl u := by
        rcases x with v | ⟨e, i⟩
        · by_cases h : v = u
          · rw [h]
          · simp [Dp, h] at h0
        · exact absurd h0 (by have := Dp_inr_pos hr u e i; omega)
      subst this
      simp
    | succ m ih =>
      intro x hx hm
      have hxa : Dp r u x ≤ a := hx
      obtain ⟨y, hxy, hy⟩ := Dp_pred hr u x m (by omega) hm
      have hyS : y ∈ VS r a u := by show Dp r u y ≤ a; omega
      have h1 := ih y hyS hy
      have h2 := edist_adj_le G (VS r a u) y x hyS hx (hG hxy.symm)
      calc _ ≤ _ := SimpleGraph.edist_triangle
        _ ≤ (m : ℕ∞) + 1 := add_le_add h1 h2
        _ = ((m + 1 : ℕ) : ℕ∞) := by push_cast; rfl
  intro v
  have := key (Dp r u v.1) v.1 v.2 rfl
  exact this.trans (by exact_mod_cast v.2)

lemma path_edist {r n : ℕ} (G : SimpleGraph (KV r n)) (hG : KG r n ≤ G) (S : Set (KV r n))
    (f : KE n) (lo hiB : ℕ)
    (hS : ∀ i : Fin (r - 1 + 1), lo ≤ i.val → i.val ≤ hiB → (Sum.inr ⟨f, i⟩ : KV r n) ∈ S) :
    ∀ k : ℕ, ∀ (i j : Fin (r - 1 + 1)) (h1 : lo ≤ i.val) (h2 : j.val ≤ hiB)
      (h3 : i.val + k = j.val),
      (G.induce S).edist ⟨Sum.inr ⟨f, i⟩, hS i (by omega) (by omega)⟩
        ⟨Sum.inr ⟨f, j⟩, hS j (by omega) (by omega)⟩ ≤ k := by
  intro k
  induction k with
  | zero =>
    intro i j _ _ h
    have : i = j := Fin.ext (by omega)
    subst this
    simp
  | succ k ih =>
    intro i j hlo hj h
    have hj2 := j.2
    let j' : Fin (r - 1 + 1) := ⟨j.val - 1, by omega⟩
    have h1 := ih i j' hlo (by show j.val - 1 ≤ hiB; omega) (by show i.val + k = j.val - 1; omega)
    have h2 := edist_adj_le G S (Sum.inr ⟨f, j'⟩) (Sum.inr ⟨f, j⟩) (hS j' (by show lo ≤ j.val - 1; omega)
      (by show j.val - 1 ≤ hiB; omega)) (hS j (by omega) (by omega))
      (hG (by rw [KG_adj_inr_inr]; exact ⟨rfl, Or.inl (by show j.val - 1 + 1 = j.val; omega)⟩))
    calc _ ≤ _ := SimpleGraph.edist_triangle
      _ ≤ (k : ℕ∞) + 1 := add_le_add h1 h2
      _ = ((k + 1 : ℕ) : ℕ∞) := by push_cast; rfl

end FatFlat.Dev.Obs2
end

section
set_option autoImplicit false

namespace FatFlat.Dev.Obs2
open FatFlat.Hereditary

lemma radius_conn {V : Type} {G : SimpleGraph V} {S : Set V} {d : ℕ} (h : RadiusLE G S d) :
    (G.induce S).Connected := by
  obtain ⟨c, hc⟩ := h
  have : Nonempty ↥S := ⟨c⟩
  refine SimpleGraph.Connected.mk ?_
  have hr : ∀ v : ↥S, (G.induce S).Reachable c v := fun v =>
    SimpleGraph.edist_ne_top_iff_reachable.mp (ne_top_of_le_ne_top (by simp) (hc v))
  intro x y
  exact (hr x).symm.trans (hr y)

lemma ES_radius {r n : ℕ} (G : SimpleGraph (KV r n)) (hG : KG r n ≤ G) (a d : ℕ)
    (ha : 1 ≤ a) (ha2 : 2 * a ≤ r + 1) (hd : (r + 2 - 2 * a) / 2 ≤ d) (f : KE n) :
    RadiusLE G (ES r a f) d := by
  have hS : ∀ i : Fin (r - 1 + 1), a - 1 ≤ i.val → i.val ≤ r - a →
      (Sum.inr ⟨f, i⟩ : KV r n) ∈ ES r a f := by
    intro i h1 h2
    exact ⟨i, by omega, by omega, rfl⟩
  obtain ⟨c, hcv⟩ : ∃ c : Fin (r - 1 + 1), c.val = (r - 1) / 2 := ⟨⟨(r - 1) / 2, by omega⟩, rfl⟩
  have hc : (Sum.inr ⟨f, c⟩ : KV r n) ∈ ES r a f := hS c (by omega) (by omega)
  refine ⟨⟨_, hc⟩, ?_⟩
  rintro ⟨v, j, hj1, hj2, rfl⟩
  have hjS := hS j (by omega) (by omega)
  by_cases hcj : c.val ≤ j.val
  · have := path_edist G hG (ES r a f) f (a - 1) (r - a) hS (j.val - c.val) c j
      (by omega) (by omega) (by omega)
    refine this.trans ?_
    have : j.val - c.val ≤ d := by omega
    exact_mod_cast this
  · have := path_edist G hG (ES r a f) f (a - 1) (r - a) hS (c.val - j.val) j c
      (by omega) (by omega) (by omega)
    rw [SimpleGraph.edist_comm]
    refine this.trans ?_
    have : c.val - j.val ≤ d := by omega
    exact_mod_cast this


lemma edist_far {r n : ℕ} (G : SimpleGraph (KV r n)) (hGW : G ≤ WG r n) (f : KV r n → ℕ)
    (hf : Lip (WG r n) f) (x y : KV r n) (c d : ℕ) (hx : f x ≤ c) (hy : c + d ≤ f y) :
    (d : ℕ∞) ≤ G.edist x y := by
  have h1 := hf.edist_ge x y c d hx hy
  have h2 := SimpleGraph.edist_anti hGW (u := x) (v := y)
  rw [SimpleGraph.edist_comm] at h1
  exact h1.trans h2

lemma VS_far_VS {r n : ℕ} (hr : 3 ≤ r) (G : SimpleGraph (KV r n)) (hGW : G ≤ WG r n)
    (a δ : ℕ) (h : a + δ + a ≤ r + 1) (ha : a ≤ r) (u v : Fin n) (huv : u ≠ v)
    (x y : KV r n) (hx : x ∈ VS r a u) (hy : y ∈ VS r a v) : (δ : ℕ∞) ≤ G.edist x y := by
  refine edist_far G hGW (Dp r u) (Dp_lipW hr u) x y a δ hx ?_
  have hy' : Dp r v y ≤ a := hy
  rcases y with w | ⟨e, i⟩
  · simp only [Dp] at hy' ⊢
    by_cases hw : w = v
    · subst hw
      rw [if_neg (Ne.symm huv)]; omega
    · rw [if_neg hw] at hy'; omega
  · have hi := i.2
    have h12 := e12_ne e
    simp only [Dp] at hy' ⊢
    split_ifs at hy' ⊢ <;> first | omega | grind

lemma VS_far_ES {r n : ℕ} (hr : 3 ≤ r) (G : SimpleGraph (KV r n)) (hGW : G ≤ WG r n)
    (a δ : ℕ) (h : a + δ ≤ r + 1) (u : Fin n) (f : KE n) (hu : ¬ (u = e1 f ∨ u = e2 f))
    (x y : KV r n) (hx : x ∈ VS r a u) (hy : y ∈ ES r a f) : (δ : ℕ∞) ≤ G.edist x y := by
  refine edist_far G hGW (Dp r u) (Dp_lipW hr u) x y a δ hx ?_
  obtain ⟨i, _, _, rfl⟩ := hy
  simp only [Dp]
  rw [if_neg (fun h' => hu (Or.inl h')), if_neg (fun h' => hu (Or.inr h'))]
  omega

lemma ES_far_ES {r n : ℕ} (hr : 3 ≤ r) (G : SimpleGraph (KV r n)) (hGW : G ≤ WG r n)
    (a δ : ℕ) (ha : 1 ≤ a) (h2 : δ + 1 ≤ 2 * a) (h3 : δ ≤ r - 1) (f f' : KE n) (hff : f ≠ f')
    (x y : KV r n) (hx : x ∈ ES r a f) (hy : y ∈ ES r a f') : (δ : ℕ∞) ≤ G.edist x y := by
  refine edist_far G hGW (Fe r a (a + δ) f) (Fe_lipW hr f a (a + δ) ha (by omega) (by omega))
    x y 0 δ ?_ ?_
  · obtain ⟨i, h1, h2, rfl⟩ := hx
    have h12 := e12_ne f
    simp only [Fe, Nf, Dp]
    simp only [if_true, eq_self_iff_true]
    rw [if_neg (Ne.symm h12)]
    omega
  · obtain ⟨i, h1, h2, rfl⟩ := hy
    have h12 := e12_ne f'
    simp only [Fe, Nf, Dp]
    rw [if_neg (Ne.symm hff)]
    split_ifs <;> first | omega | grind

lemma VS_meet {r n : ℕ} (hr : 3 ≤ r) (a : ℕ) (ha : 1 ≤ a) (ha2 : 2 * a ≤ r + 1) (f : KE n)
    (u : Fin n) (hu : u = e1 f ∨ u = e2 f) : (ES r a f ∩ VS r a u).Nonempty := by
  have h12 := e12_ne f
  rcases hu with rfl | rfl
  · refine ⟨Sum.inr ⟨f, ⟨a - 1, by omega⟩⟩, ⟨⟨a - 1, by omega⟩, by simp; omega, by simp; omega, rfl⟩, ?_⟩
    simp [VS, Dp]; omega
  · refine ⟨Sum.inr ⟨f, ⟨r - a, by omega⟩⟩, ⟨⟨r - a, by omega⟩, by simp; omega, by simp; omega, rfl⟩, ?_⟩
    simp [VS, Dp, Ne.symm h12]; omega

end FatFlat.Dev.Obs2
end

section
set_option autoImplicit false

namespace FatFlat.Dev.Obs2
open FatFlat.Hereditary

lemma radius_mono {V : Type} {G : SimpleGraph V} {S : Set V} {d d' : ℕ} (h : RadiusLE G S d)
    (hd : d ≤ d') : RadiusLE G S d' := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun v => (hc v).trans (by exact_mod_cast hd)⟩

def toK {n : ℕ} (H : SimpleGraph (Fin n)) (e : H.edgeSet) : KE n :=
  ⟨e.1, SimpleGraph.edgeSet_mono le_top e.2⟩

theorem model {r n : ℕ} (hr : 3 ≤ r) (a δ d : ℕ) (ha : 1 ≤ a) (ha2 : 2 * a ≤ r + 1)
    (h2 : δ + 1 ≤ 2 * a) (h4 : a + δ + a ≤ r + 1) (h3 : δ ≤ r - 1) (had : a ≤ d)
    (hd : (r + 2 - 2 * a) / 2 ≤ d) (G : SimpleGraph (KV r n)) (hKG : KG r n ≤ G)
    (hGW : G ≤ WG r n) (H : SimpleGraph (Fin n)) : IsShallowFatMinor H G d δ := by
  let φ : Fin n ⊕ H.edgeSet → Set (KV r n)
    | Sum.inl w => VS r a w
    | Sum.inr e => ES r a (toK H e)
  have hrad : ∀ o, RadiusLE G (φ o) d := by
    intro o
    rcases o with w | e
    · exact radius_mono (VS_radius hr G hKG a (by omega) w) had
    · exact ES_radius G hKG a d ha ha2 hd (toK H e)
  refine ⟨⟨φ, ?_, ?_, ?_, ?_⟩, hrad⟩
  · intro o
    obtain ⟨c, _⟩ := hrad o
    exact ⟨c.1, c.2⟩
  · intro o
    exact radius_conn (hrad o)
  · intro e u hu
    exact VS_meet hr a ha ha2 (toK H e) u ((mem_iff (toK H e) u).mp hu)
  · intro o₁ o₂ hne hinc x hx y hy
    rcases o₁ with u | e <;> rcases o₂ with v | e'
    · have huv : u ≠ v := fun h => hne (by rw [h])
      exact VS_far_VS hr G hGW a δ h4 (by omega) u v huv x y hx hy
    · have hu : ¬ (u = e1 (toK H e') ∨ u = e2 (toK H e')) := by
        rw [← mem_iff]; exact hinc
      exact VS_far_ES hr G hGW a δ (by omega) u (toK H e') hu x y hx hy
    · have hu : ¬ (v = e1 (toK H e) ∨ v = e2 (toK H e)) := by
        rw [← mem_iff]; exact hinc
      rw [SimpleGraph.edist_comm]
      exact VS_far_ES hr G hGW a δ (by omega) v (toK H e) hu y x hy hx
    · have hff : toK H e ≠ toK H e' := by
        intro h
        apply hne
        congr 1
        exact Subtype.ext (by simpa [toK] using h)
      exact ES_far_ES hr G hGW a δ ha h2 h3 _ _ hff x y hx hy

end FatFlat.Dev.Obs2

namespace FatFlat.Hereditary
open FatFlat.Dev.Obs2 in
theorem chk_observation_2 (r n : ℕ) (hr : 3 ≤ r) (H : SimpleGraph (Fin n)) :
    IsShallowFatMinor H (subdividedClique r n) (r / 4 + 10) (r / 2 - 10) ∧
    IsShallowFatMinor H (web r n) (r / 4 + 10) (r / 2 - 10) := by
  have key : ∀ G : SimpleGraph (KV r n), KG r n ≤ G → G ≤ WG r n →
      IsShallowFatMinor H G (r / 4 + 10) (r / 2 - 10) := fun G h1 h2 =>
    model hr ((r / 2 - 10) / 2 + 1) (r / 2 - 10) (r / 4 + 10) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) G h1 h2 H
  exact ⟨key (KG r n) le_rfl (KG_le_WG r n), key (WG r n) (KG_le_WG r n) le_rfl⟩
end FatFlat.Hereditary
end

theorem solution : type_of% @FatFlat.Hereditary.chk_observation_2 := @FatFlat.Hereditary.chk_observation_2
