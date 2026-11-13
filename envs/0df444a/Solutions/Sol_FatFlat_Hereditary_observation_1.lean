-- Prove2me | solution 1 for FatFlat.Hereditary.observation_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:33:29.481197+00:00
-- url     : https://prove2.me/submissions/cb4da51b-48e6-4af4-9d98-61039c9083d1

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Classes

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

namespace FatFlat.Dev.Emb
open SparseDisc

section split
variable {W : Type} (H : SimpleGraph W) (t : ℕ)

/-- the 1-subdivision of `H` (constant `0`) -/
noncomputable abbrev J := SD H 0

/-- first (out) endpoint of the edge `e` -/
noncomputable def oa (e : H.edgeSet) : W := (Quot.out (e : Sym2 W)).1
/-- second (out) endpoint of the edge `e` -/
noncomputable def ob (e : H.edgeSet) : W := (Quot.out (e : Sym2 W)).2

lemma oa_ne_ob (e : H.edgeSet) : oa H e ≠ ob H e := out_ne e

/-- the subdivision vertex of `e` in `J` -/
noncomputable def cv (e : H.edgeSet) : W ⊕ Σ _ : H.edgeSet, Fin (0 + 1) := Sum.inr ⟨e, 0⟩

/-- the edge of `J` from `oa e` to `cv e` -/
noncomputable def el (e : H.edgeSet) : (J H).edgeSet :=
  ⟨s(Sum.inl (oa H e), cv H e),
    (SimpleGraph.mem_edgeSet _).2 ((SD_adj_inl_inr H 0 _ e 0).2 (Or.inl ⟨rfl, rfl⟩))⟩

/-- the edge of `J` from `ob e` to `cv e` -/
noncomputable def er (e : H.edgeSet) : (J H).edgeSet :=
  ⟨s(Sum.inl (ob H e), cv H e),
    (SimpleGraph.mem_edgeSet _).2 ((SD_adj_inl_inr H 0 _ e 0).2 (Or.inr ⟨rfl, rfl⟩))⟩

lemma cv_inj {e e' : H.edgeSet} (h : cv H e = cv H e') : e = e' := by
  simp only [cv, Sum.inr.injEq, Sigma.mk.inj_iff] at h
  exact h.1

lemma el_inj {e e' : H.edgeSet} (h : el H e = el H e') : e = e' := by
  have h := congrArg Subtype.val h
  simp only [el, Sym2.eq_iff] at h
  rcases h with ⟨-, h⟩ | ⟨h, -⟩
  · exact cv_inj H h
  · simp [cv] at h

lemma er_inj {e e' : H.edgeSet} (h : er H e = er H e') : e = e' := by
  have h := congrArg Subtype.val h
  simp only [er, Sym2.eq_iff] at h
  rcases h with ⟨-, h⟩ | ⟨h, -⟩
  · exact cv_inj H h
  · simp [cv] at h

lemma el_ne_er (e e' : H.edgeSet) : el H e ≠ er H e' := by
  intro h
  have h := congrArg Subtype.val h
  simp only [el, er, Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h, -⟩
  · have := cv_inj H h2
    subst this
    exact oa_ne_ob H e (Sum.inl.inj h1)
  · simp [cv] at h

/-- vertices of `J H` -/
abbrev VJ (H : SimpleGraph W) := W ⊕ Σ _ : H.edgeSet, Fin (0 + 1)
/-- vertices of the `t`-subdivision of `J H` -/
abbrev VT (H : SimpleGraph W) (t : ℕ) := VJ H ⊕ Σ _ : (J H).edgeSet, Fin (t + 1)

variable {H}

lemma el_val (e : H.edgeSet) : ((el H e : (J H).edgeSet) : Sym2 (VJ H)) = s(Sum.inl (oa H e), cv H e) := rfl
lemma er_val (e : H.edgeSet) : ((er H e : (J H).edgeSet) : Sym2 (VJ H)) = s(cv H e, Sum.inl (ob H e)) := by
  rw [Sym2.eq_swap]; rfl

lemma inl_ne_cv (u : W) (e : H.edgeSet) : (Sum.inl u : VJ H) ≠ cv H e := by simp [cv]
lemma cv_ne_inl (u : W) (e : H.edgeSet) : cv H e ≠ (Sum.inl u : VJ H) := by simp [cv]
@[simp] lemma cv_inj_iff {e e' : H.edgeSet} : cv H e = cv H e' ↔ e = e' :=
  ⟨cv_inj H, fun h => by rw [h]⟩

open Classical in
/-- left segment vertex -/
noncomputable def lv (e : H.edgeSet) (j : Fin (t + 1)) : VT H t :=
  Sum.inr ⟨el H e, pos (J H) t (el H e) (Sum.inl (oa H e)) j⟩

open Classical in
/-- right segment vertex -/
noncomputable def rv (e : H.edgeSet) (j : Fin (t + 1)) : VT H t :=
  Sum.inr ⟨er H e, pos (J H) t (er H e) (cv H e) j⟩

/-- the middle vertex -/
noncomputable def mv (e : H.edgeSet) : VT H t := Sum.inl (cv H e)

/-- a principal vertex of `H` -/
def pv (t : ℕ) (u : W) : VT H t := Sum.inl (Sum.inl u)

open Classical in
lemma adj_pv_lv (u : W) (e : H.edgeSet) (j : Fin (t + 1)) :
    (SD (J H) t).Adj (pv t u) (lv t e j) ↔ u = oa H e ∧ j.val = 0 := by
  unfold pv lv
  rw [pos_adj_inl (J H) t (el H e) _ (cv H e) (el_val e) (by simp [cv])]
  simp [inl_ne_cv]

open Classical in
lemma adj_pv_rv (u : W) (e : H.edgeSet) (j : Fin (t + 1)) :
    (SD (J H) t).Adj (pv t u) (rv t e j) ↔ u = ob H e ∧ j.val = t := by
  unfold pv rv
  rw [pos_adj_inl (J H) t (er H e) (cv H e) (Sum.inl (ob H e)) (er_val e) (by simp [cv])]
  simp [inl_ne_cv]

open Classical in
lemma adj_mv_lv (e e' : H.edgeSet) (j : Fin (t + 1)) :
    (SD (J H) t).Adj (mv t e) (lv t e' j) ↔ e = e' ∧ j.val = t := by
  unfold mv lv
  rw [pos_adj_inl (J H) t (el H e') _ (cv H e') (el_val e') (by simp [cv])]
  simp [inl_ne_cv, cv_ne_inl]

open Classical in
lemma adj_mv_rv (e e' : H.edgeSet) (j : Fin (t + 1)) :
    (SD (J H) t).Adj (mv t e) (rv t e' j) ↔ e = e' ∧ j.val = 0 := by
  unfold mv rv
  rw [pos_adj_inl (J H) t (er H e') (cv H e') (Sum.inl (ob H e')) (er_val e') (by simp [cv])]
  simp [inl_ne_cv, cv_ne_inl]

lemma adj_pv_mv (u : W) (e : H.edgeSet) : ¬ (SD (J H) t).Adj (pv t u) (mv t e) :=
  SD_adj_inl_inl _ _ _ _

lemma adj_pv_pv (u v : W) : ¬ (SD (J H) t).Adj (pv t u) (pv t v) :=
  SD_adj_inl_inl _ _ _ _

lemma adj_mv_mv (e e' : H.edgeSet) : ¬ (SD (J H) t).Adj (mv t e) (mv t e') :=
  SD_adj_inl_inl _ _ _ _

open Classical in
lemma adj_lv_lv (e e' : H.edgeSet) (j j' : Fin (t + 1)) :
    (SD (J H) t).Adj (lv t e j) (lv t e' j') ↔ e = e' ∧ (j.val + 1 = j'.val ∨ j'.val + 1 = j.val) := by
  unfold lv
  by_cases h : e = e'
  · subst h
    rw [pos_adj_inr]; simp
  · have : el H e ≠ el H e' := fun h' => h (el_inj H h')
    rw [SD_adj_inr_inr]; simp [this, h]

open Classical in
lemma adj_rv_rv (e e' : H.edgeSet) (j j' : Fin (t + 1)) :
    (SD (J H) t).Adj (rv t e j) (rv t e' j') ↔ e = e' ∧ (j.val + 1 = j'.val ∨ j'.val + 1 = j.val) := by
  unfold rv
  by_cases h : e = e'
  · subst h
    rw [pos_adj_inr]; simp
  · have : er H e ≠ er H e' := fun h' => h (er_inj H h')
    rw [SD_adj_inr_inr]; simp [this, h]

open Classical in
lemma adj_lv_rv (e e' : H.edgeSet) (j j' : Fin (t + 1)) :
    ¬ (SD (J H) t).Adj (lv t e j) (rv t e' j') := by
  unfold lv rv
  rw [SD_adj_inr_inr]
  rintro ⟨h, -⟩
  exact el_ne_er H e e' (by simpa using h)


/-- The vertex map of the splitting embedding with a middle vertex. -/
noncomputable def splitMapM (t : ℕ) :
    (W ⊕ Σ _ : H.edgeSet, Fin (2 * t + 2 + 1)) → VT H t
  | Sum.inl u => pv t u
  | Sum.inr ⟨e, i⟩ =>
      if h : i.val < t + 1 then lv t e ⟨i.val, h⟩
      else if i.val = t + 1 then mv t e
      else rv t e ⟨i.val - (t + 2), by have := i.isLt; omega⟩

lemma splitMapM_lt (t : ℕ) (e : H.edgeSet) (i : Fin (2 * t + 2 + 1)) (h : i.val < t + 1) :
    splitMapM t (Sum.inr ⟨e, i⟩) = lv t e ⟨i.val, h⟩ := by
  simp [splitMapM, h]

lemma splitMapM_eq (t : ℕ) (e : H.edgeSet) (i : Fin (2 * t + 2 + 1)) (h : i.val = t + 1) :
    splitMapM t (Sum.inr ⟨e, i⟩) = mv t e := by
  simp [splitMapM, h]

lemma splitMapM_gt (t : ℕ) (e : H.edgeSet) (i : Fin (2 * t + 2 + 1)) (h : t + 1 < i.val) :
    splitMapM t (Sum.inr ⟨e, i⟩) = rv t e ⟨i.val - (t + 2), by have := i.isLt; omega⟩ := by
  simp [splitMapM, show ¬ i.val < t + 1 by omega, show ¬ i.val = t + 1 by omega]

lemma sd_adj_oa (k : ℕ) (u : W) (e : H.edgeSet) (i : Fin (k + 1)) :
    (SD H k).Adj (Sum.inl u) (Sum.inr ⟨e, i⟩) ↔
      (u = oa H e ∧ i.val = 0) ∨ (u = ob H e ∧ i.val = k) :=
  SD_adj_inl_inr H k u e i

theorem splitMapM_adj (t : ℕ) (x y : W ⊕ Σ _ : H.edgeSet, Fin (2 * t + 2 + 1)) :
    (SD (J H) t).Adj (splitMapM t x) (splitMapM t y) ↔ (SD H (2 * t + 2)).Adj x y := by
  have key : ∀ (u : W) (e' : H.edgeSet) (j : Fin (2 * t + 2 + 1)),
      (SD (J H) t).Adj (splitMapM t (Sum.inl u)) (splitMapM t (Sum.inr ⟨e', j⟩)) ↔
        (SD H (2 * t + 2)).Adj (Sum.inl u) (Sum.inr ⟨e', j⟩) := by
    intro u e' j
    rw [sd_adj_oa]
    rcases lt_trichotomy j.val (t + 1) with h | h | h
    · rw [splitMapM_lt t e' j h]
      show (SD (J H) t).Adj (pv t u) _ ↔ _
      rw [adj_pv_lv]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | ⟨-, h'⟩)
        · exact h
        · omega
    · rw [splitMapM_eq t e' j h]
      show (SD (J H) t).Adj (pv t u) _ ↔ _
      exact iff_of_false (adj_pv_mv t u e') (by rintro (⟨-, h'⟩ | ⟨-, h'⟩) <;> omega)
    · rw [splitMapM_gt t e' j h]
      show (SD (J H) t).Adj (pv t u) _ ↔ _
      rw [adj_pv_rv]
      constructor
      · rintro ⟨h1, h2⟩; exact Or.inr ⟨h1, by simp at h2; omega⟩
      · rintro (⟨-, h'⟩ | ⟨h1, h2⟩)
        · omega
        · exact ⟨h1, by simp; omega⟩
  rcases x with u | ⟨e, i⟩
  · rcases y with v | ⟨e', j⟩
    · simp only [splitMapM]
      exact iff_of_false (adj_pv_pv t u v) (SD_adj_inl_inl _ _ _ _)
    · exact key u e' j
  · rcases y with v | ⟨e', j⟩
    · rw [SimpleGraph.adj_comm, SimpleGraph.adj_comm (SD H _)]
      exact key v e i
    · rw [SD_adj_inr_inr]
      rcases lt_trichotomy i.val (t + 1) with h | h | h <;>
      rcases lt_trichotomy j.val (t + 1) with h' | h' | h'
      · rw [splitMapM_lt t e i h, splitMapM_lt t e' j h', adj_lv_lv]
      · rw [splitMapM_lt t e i h, splitMapM_eq t e' j h', SimpleGraph.adj_comm, adj_mv_lv]
        constructor <;> rintro ⟨rfl, hh⟩ <;> exact ⟨rfl, by (try simp only [Fin.val_mk] at hh ⊢); omega⟩
      · rw [splitMapM_lt t e i h, splitMapM_gt t e' j h']
        exact iff_of_false (adj_lv_rv _ _ _ _ _) (by rintro ⟨-, h⟩; omega)
      · rw [splitMapM_eq t e i h, splitMapM_lt t e' j h', adj_mv_lv]
        constructor <;> rintro ⟨rfl, hh⟩ <;> exact ⟨rfl, by (try simp only [Fin.val_mk] at hh ⊢); omega⟩
      · rw [splitMapM_eq t e i h, splitMapM_eq t e' j h']
        exact iff_of_false (adj_mv_mv _ _ _) (by rintro ⟨-, h⟩; omega)
      · rw [splitMapM_eq t e i h, splitMapM_gt t e' j h', adj_mv_rv]
        constructor <;> rintro ⟨rfl, hh⟩ <;> exact ⟨rfl, by (try simp only [Fin.val_mk] at hh ⊢); omega⟩
      · rw [splitMapM_gt t e i h, splitMapM_lt t e' j h']
        exact iff_of_false (fun hh => adj_lv_rv _ _ _ _ _ hh.symm)
          (by rintro ⟨-, h⟩; omega)
      · rw [splitMapM_gt t e i h, splitMapM_eq t e' j h', SimpleGraph.adj_comm, adj_mv_rv]
        constructor <;> rintro ⟨rfl, hh⟩ <;> exact ⟨rfl, by (try simp only [Fin.val_mk] at hh ⊢); omega⟩
      · rw [splitMapM_gt t e i h, splitMapM_gt t e' j h', adj_rv_rv]
        constructor <;> rintro ⟨rfl, hh⟩ <;> exact ⟨rfl, by (try simp only [Fin.val_mk] at hh ⊢); omega⟩


open Classical in
lemma lv_inj {e e' : H.edgeSet} {j j' : Fin (t + 1)} (h : lv t e j = lv t e' j') :
    e = e' ∧ j = j' := by
  simp only [lv, Sum.inr.injEq, Sigma.mk.inj_iff] at h
  obtain ⟨h1, h2⟩ := h
  have := el_inj H h1
  subst this
  simp only [heq_eq_eq] at h2
  exact ⟨rfl, (pos_inj _ _ _ _ _ _).1 h2⟩

open Classical in
lemma rv_inj {e e' : H.edgeSet} {j j' : Fin (t + 1)} (h : rv t e j = rv t e' j') :
    e = e' ∧ j = j' := by
  simp only [rv, Sum.inr.injEq, Sigma.mk.inj_iff] at h
  obtain ⟨h1, h2⟩ := h
  have := er_inj H h1
  subst this
  simp only [heq_eq_eq] at h2
  exact ⟨rfl, (pos_inj _ _ _ _ _ _).1 h2⟩

lemma lv_ne_rv (e e' : H.edgeSet) (j j' : Fin (t + 1)) : lv t e j ≠ rv t e' j' := by
  intro h
  simp only [lv, rv, Sum.inr.injEq, Sigma.mk.inj_iff] at h
  exact el_ne_er H e e' h.1

lemma lv_ne_mv (e e' : H.edgeSet) (j : Fin (t + 1)) : lv t e j ≠ mv t e' := by
  simp [lv, mv]

lemma rv_ne_mv (e e' : H.edgeSet) (j : Fin (t + 1)) : rv t e j ≠ mv t e' := by
  simp [rv, mv]

lemma pv_ne_lv (u : W) (e : H.edgeSet) (j : Fin (t + 1)) : pv t u ≠ lv t e j := by
  simp [lv, pv]

lemma pv_ne_rv (u : W) (e : H.edgeSet) (j : Fin (t + 1)) : pv t u ≠ rv t e j := by
  simp [rv, pv]

lemma pv_ne_mv (u : W) (e : H.edgeSet) : pv t u ≠ mv t e := by
  simp [mv, pv, cv]

lemma pv_inj {u v : W} (h : pv (H := H) t u = pv t v) : u = v := by
  simpa [pv] using h

theorem splitMapM_inj (t : ℕ) : Function.Injective (splitMapM (H := H) t) := by
  rintro (u | ⟨e, i⟩) (v | ⟨e', j⟩) h
  · exact congrArg _ (pv_inj t h)
  · exfalso
    rcases lt_trichotomy j.val (t + 1) with h' | h' | h'
    · rw [splitMapM_lt t e' j h'] at h; exact pv_ne_lv t _ _ _ h
    · rw [splitMapM_eq t e' j h'] at h; exact pv_ne_mv t _ _ h
    · rw [splitMapM_gt t e' j h'] at h; exact pv_ne_rv t _ _ _ h
  · exfalso
    rcases lt_trichotomy i.val (t + 1) with h' | h' | h'
    · rw [splitMapM_lt t e i h'] at h; exact pv_ne_lv t _ _ _ h.symm
    · rw [splitMapM_eq t e i h'] at h; exact pv_ne_mv t _ _ h.symm
    · rw [splitMapM_gt t e i h'] at h; exact pv_ne_rv t _ _ _ h.symm
  · rcases lt_trichotomy i.val (t + 1) with h1 | h1 | h1 <;>
    rcases lt_trichotomy j.val (t + 1) with h2 | h2 | h2
    · rw [splitMapM_lt t e i h1, splitMapM_lt t e' j h2] at h
      obtain ⟨rfl, h3⟩ := lv_inj t h
      simp only [Fin.mk.injEq] at h3
      rw [Fin.ext h3]
    · rw [splitMapM_lt t e i h1, splitMapM_eq t e' j h2] at h; exact absurd h (lv_ne_mv t _ _ _)
    · rw [splitMapM_lt t e i h1, splitMapM_gt t e' j h2] at h; exact absurd h (lv_ne_rv t _ _ _ _)
    · rw [splitMapM_eq t e i h1, splitMapM_lt t e' j h2] at h; exact absurd h.symm (lv_ne_mv t _ _ _)
    · rw [splitMapM_eq t e i h1, splitMapM_eq t e' j h2] at h
      have : e = e' := cv_inj H (Sum.inl.inj h)
      subst this
      rw [Fin.ext (h1.trans h2.symm)]
    · rw [splitMapM_eq t e i h1, splitMapM_gt t e' j h2] at h; exact absurd h.symm (rv_ne_mv t _ _ _)
    · rw [splitMapM_gt t e i h1, splitMapM_lt t e' j h2] at h; exact absurd h.symm (lv_ne_rv t _ _ _ _)
    · rw [splitMapM_gt t e i h1, splitMapM_eq t e' j h2] at h; exact absurd h (rv_ne_mv t _ _ _)
    · rw [splitMapM_gt t e i h1, splitMapM_gt t e' j h2] at h
      obtain ⟨rfl, h3⟩ := rv_inj t h
      simp only [Fin.mk.injEq] at h3
      have : i = j := Fin.ext (by omega)
      rw [this]

/-- Splitting embedding with a middle vertex: `S_{2t+2}(H) ↪ S_t(S_0(H))`. -/
noncomputable def splitEmbM (H : SimpleGraph W) (t : ℕ) : SD H (2 * t + 2) ↪g SD (J H) t where
  toFun := splitMapM t
  inj' := splitMapM_inj t
  map_rel_iff' := splitMapM_adj t _ _


section skip
open FatFlat.Hereditary

/-- the web of `S_t(J H)` with cliques at the middle vertices only -/
noncomputable abbrev WC (H : SimpleGraph W) (t : ℕ) : SimpleGraph (VT H t) :=
  webOf (SD (J H) t) (Set.range (mv t))

lemma wc_adj (x y : VT H t) :
    (WC H t).Adj x y ↔ (SD (J H) t).Adj x y ∨
      (x ≠ y ∧ ∃ e, (SD (J H) t).Adj (mv t e) x ∧ (SD (J H) t).Adj (mv t e) y) := by
  rw [webOf_adj]
  apply or_congr Iff.rfl
  apply and_congr Iff.rfl
  constructor
  · rintro ⟨_, ⟨e, rfl⟩, h⟩; exact ⟨e, h⟩
  · rintro ⟨e, h⟩; exact ⟨_, ⟨e, rfl⟩, h⟩

lemma wc_pv_lv (u : W) (e : H.edgeSet) (j : Fin (t + 1)) :
    (WC H t).Adj (pv t u) (lv t e j) ↔ u = oa H e ∧ j.val = 0 := by
  rw [wc_adj, adj_pv_lv]
  simp only [or_iff_left_iff_imp]
  rintro ⟨-, e', h, -⟩
  exact (adj_pv_mv t u e' h.symm).elim

lemma wc_pv_rv (u : W) (e : H.edgeSet) (j : Fin (t + 1)) :
    (WC H t).Adj (pv t u) (rv t e j) ↔ u = ob H e ∧ j.val = t := by
  rw [wc_adj, adj_pv_rv]
  simp only [or_iff_left_iff_imp]
  rintro ⟨-, e', h, -⟩
  exact (adj_pv_mv t u e' h.symm).elim

lemma wc_pv_pv (u v : W) : ¬ (WC H t).Adj (pv t u) (pv t v) := by
  rw [wc_adj]
  rintro (h | ⟨-, e', h, -⟩)
  · exact adj_pv_pv t u v h
  · exact adj_pv_mv t u e' h.symm

lemma wc_lv_lv (e e' : H.edgeSet) (j j' : Fin (t + 1)) :
    (WC H t).Adj (lv t e j) (lv t e' j') ↔
      e = e' ∧ (j.val + 1 = j'.val ∨ j'.val + 1 = j.val) := by
  rw [wc_adj, adj_lv_lv]
  simp only [or_iff_left_iff_imp]
  rintro ⟨hne, e'', h1, h2⟩
  rw [adj_mv_lv] at h1 h2
  obtain ⟨rfl, hj⟩ := h1
  obtain ⟨rfl, hj'⟩ := h2
  exact absurd (by rw [Fin.ext (hj.trans hj'.symm : j.val = j'.val)]) hne

lemma wc_rv_rv (e e' : H.edgeSet) (j j' : Fin (t + 1)) :
    (WC H t).Adj (rv t e j) (rv t e' j') ↔
      e = e' ∧ (j.val + 1 = j'.val ∨ j'.val + 1 = j.val) := by
  rw [wc_adj, adj_rv_rv]
  simp only [or_iff_left_iff_imp]
  rintro ⟨hne, e'', h1, h2⟩
  rw [adj_mv_rv] at h1 h2
  obtain ⟨rfl, hj⟩ := h1
  obtain ⟨rfl, hj'⟩ := h2
  exact absurd (by rw [Fin.ext (hj.trans hj'.symm : j.val = j'.val)]) hne

lemma wc_lv_rv (e e' : H.edgeSet) (j j' : Fin (t + 1)) :
    (WC H t).Adj (lv t e j) (rv t e' j') ↔ e = e' ∧ j.val = t ∧ j'.val = 0 := by
  rw [wc_adj]
  constructor
  · rintro (h | ⟨-, e'', h1, h2⟩)
    · exact (adj_lv_rv _ _ _ _ _ h).elim
    · rw [adj_mv_lv] at h1
      rw [adj_mv_rv] at h2
      obtain ⟨rfl, hj⟩ := h1
      obtain ⟨rfl, hj'⟩ := h2
      exact ⟨rfl, hj, hj'⟩
  · rintro ⟨rfl, hj, hj'⟩
    refine Or.inr ⟨(lv_ne_rv t _ _ _ _), e, ?_, ?_⟩
    · rw [adj_mv_lv]; exact ⟨rfl, hj⟩
    · rw [adj_mv_rv]; exact ⟨rfl, hj'⟩


/-- The vertex map of the splitting embedding that skips the middle vertex. -/
noncomputable def splitMapA (t : ℕ) :
    (W ⊕ Σ _ : H.edgeSet, Fin (2 * t + 1 + 1)) → VT H t
  | Sum.inl u => pv t u
  | Sum.inr ⟨e, i⟩ =>
      if h : i.val < t + 1 then lv t e ⟨i.val, h⟩
      else rv t e ⟨i.val - (t + 1), by have := i.isLt; omega⟩

lemma splitMapA_lt (t : ℕ) (e : H.edgeSet) (i : Fin (2 * t + 1 + 1)) (h : i.val < t + 1) :
    splitMapA t (Sum.inr ⟨e, i⟩) = lv t e ⟨i.val, h⟩ := by
  simp [splitMapA, h]

lemma splitMapA_ge (t : ℕ) (e : H.edgeSet) (i : Fin (2 * t + 1 + 1)) (h : t + 1 ≤ i.val) :
    splitMapA t (Sum.inr ⟨e, i⟩) = rv t e ⟨i.val - (t + 1), by have := i.isLt; omega⟩ := by
  simp [splitMapA, show ¬ i.val < t + 1 by omega]

theorem splitMapA_adj (t : ℕ) (x y : W ⊕ Σ _ : H.edgeSet, Fin (2 * t + 1 + 1)) :
    (WC H t).Adj (splitMapA t x) (splitMapA t y) ↔ (SD H (2 * t + 1)).Adj x y := by
  have key : ∀ (u : W) (e' : H.edgeSet) (j : Fin (2 * t + 1 + 1)),
      (WC H t).Adj (splitMapA t (Sum.inl u)) (splitMapA t (Sum.inr ⟨e', j⟩)) ↔
        (SD H (2 * t + 1)).Adj (Sum.inl u) (Sum.inr ⟨e', j⟩) := by
    intro u e' j
    rw [sd_adj_oa]
    by_cases h : j.val < t + 1
    · rw [splitMapA_lt t e' j h]
      show (WC H t).Adj (pv t u) _ ↔ _
      rw [wc_pv_lv]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | ⟨-, h'⟩)
        · exact h
        · omega
    · rw [splitMapA_ge t e' j (by omega)]
      show (WC H t).Adj (pv t u) _ ↔ _
      rw [wc_pv_rv]
      constructor
      · rintro ⟨h1, h2⟩; exact Or.inr ⟨h1, by simp at h2; omega⟩
      · rintro (⟨-, h'⟩ | ⟨h1, h2⟩)
        · omega
        · exact ⟨h1, by simp; omega⟩
  rcases x with u | ⟨e, i⟩
  · rcases y with v | ⟨e', j⟩
    · simp only [splitMapA]
      exact iff_of_false (wc_pv_pv t u v) (SD_adj_inl_inl _ _ _ _)
    · exact key u e' j
  · rcases y with v | ⟨e', j⟩
    · rw [SimpleGraph.adj_comm, SimpleGraph.adj_comm (SD H _)]
      exact key v e i
    · rw [SD_adj_inr_inr]
      by_cases h : i.val < t + 1 <;> by_cases h' : j.val < t + 1
      · rw [splitMapA_lt t e i h, splitMapA_lt t e' j h', wc_lv_lv]
      · rw [splitMapA_lt t e i h, splitMapA_ge t e' j (by omega), wc_lv_rv]
        constructor
        · rintro ⟨rfl, h1, h2⟩; exact ⟨rfl, by simp at h1 h2; omega⟩
        · rintro ⟨rfl, hh⟩; exact ⟨rfl, by simp; omega, by simp; omega⟩
      · rw [splitMapA_ge t e i (by omega), splitMapA_lt t e' j h', SimpleGraph.adj_comm, wc_lv_rv]
        constructor
        · rintro ⟨rfl, h1, h2⟩; exact ⟨rfl, by simp at h1 h2; omega⟩
        · rintro ⟨rfl, hh⟩; exact ⟨rfl, by simp; omega, by simp; omega⟩
      · rw [splitMapA_ge t e i (by omega), splitMapA_ge t e' j (by omega), wc_rv_rv]
        constructor <;> rintro ⟨rfl, hh⟩ <;> exact ⟨rfl, by (try simp only [Fin.val_mk] at hh ⊢); omega⟩


theorem splitMapA_inj (t : ℕ) : Function.Injective (splitMapA (H := H) t) := by
  rintro (u | ⟨e, i⟩) (v | ⟨e', j⟩) h
  · exact congrArg _ (pv_inj t h)
  · exfalso
    by_cases h' : j.val < t + 1
    · rw [splitMapA_lt t e' j h'] at h; exact pv_ne_lv t _ _ _ h
    · rw [splitMapA_ge t e' j (by omega)] at h; exact pv_ne_rv t _ _ _ h
  · exfalso
    by_cases h' : i.val < t + 1
    · rw [splitMapA_lt t e i h'] at h; exact pv_ne_lv t _ _ _ h.symm
    · rw [splitMapA_ge t e i (by omega)] at h; exact pv_ne_rv t _ _ _ h.symm
  · by_cases h1 : i.val < t + 1 <;> by_cases h2 : j.val < t + 1
    · rw [splitMapA_lt t e i h1, splitMapA_lt t e' j h2] at h
      obtain ⟨rfl, h3⟩ := lv_inj t h
      simp only [Fin.mk.injEq] at h3
      rw [Fin.ext h3]
    · rw [splitMapA_lt t e i h1, splitMapA_ge t e' j (by omega)] at h
      exact absurd h (lv_ne_rv t _ _ _ _)
    · rw [splitMapA_ge t e i (by omega), splitMapA_lt t e' j h2] at h
      exact absurd h.symm (lv_ne_rv t _ _ _ _)
    · rw [splitMapA_ge t e i (by omega), splitMapA_ge t e' j (by omega)] at h
      obtain ⟨rfl, h3⟩ := rv_inj t h
      simp only [Fin.mk.injEq] at h3
      have : i = j := Fin.ext (by omega)
      rw [this]

/-- Splitting embedding skipping the middle vertex: `S_{2t+1}(H) ↪ web of S_t(S_0(H))`. -/
noncomputable def splitEmbA (H : SimpleGraph W) (t : ℕ) : SD H (2 * t + 1) ↪g WC H t where
  toFun := splitMapA t
  inj' := splitMapA_inj t
  map_rel_iff' := splitMapA_adj t _ _


lemma wc_of_adj {x y : VT H t} (h : (SD (J H) t).Adj x y) : (WC H t).Adj x y :=
  (wc_adj t x y).2 (Or.inl h)

lemma adj_of_wc_pv (u : W) (z : VT H t) (h : (WC H t).Adj (pv t u) z) :
    (SD (J H) t).Adj (pv t u) z := by
  rcases (wc_adj t _ _).1 h with h | ⟨-, e, h1, -⟩
  · exact h
  · exact (adj_pv_mv t u e h1.symm).elim

lemma web_of_wc {x y : VT H t} (h : (WC H t).Adj x y) :
    (webOf (SD (J H) t) (Set.range Sum.inl)).Adj x y := by
  rw [webOf_adj]
  rcases (wc_adj t _ _).1 h with h | ⟨hne, e, h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨hne, mv t e, ⟨cv H e, rfl⟩, h1, h2⟩

/-- Splitting embedding of webs, skipping the middle vertex:
`W(S_{2t+1}(H)) ↪ W(S_t(S_0(H)))`. -/
noncomputable def splitEmbWeb (H : SimpleGraph W) (t : ℕ) :
    webOf (SD H (2 * t + 1)) (Set.range Sum.inl) ↪g webOf (SD (J H) t) (Set.range Sum.inl) where
  toFun := splitMapA t
  inj' := splitMapA_inj t
  map_rel_iff' := by
    intro x y
    rw [webOf_adj, webOf_adj]
    constructor
    · rintro (h | ⟨hne, p', ⟨w, rfl⟩, h1, h2⟩)
      · exact Or.inl ((splitMapA_adj t x y).1 (wc_of_adj t h))
      · rcases w with u | ⟨e, i⟩
        · have h1' := (splitMapA_adj t (Sum.inl u) x).1 (wc_of_adj t h1)
          have h2' := (splitMapA_adj t (Sum.inl u) y).1 (wc_of_adj t h2)
          exact Or.inr ⟨fun h => hne (by rw [h]), Sum.inl u, ⟨u, rfl⟩, h1', h2'⟩
        · have i0 : i = 0 := Fin.ext (by have := i.isLt; show i.val = 0; omega)
          subst i0
          exact Or.inl ((splitMapA_adj t x y).1 ((wc_adj t _ _).2
            (Or.inr ⟨hne, e, h1, h2⟩)))
    · rintro (h | ⟨hne, p, ⟨u, rfl⟩, h1, h2⟩)
      · exact (webOf_adj _ _ _ _).1 (web_of_wc t ((splitMapA_adj t x y).2 h))
      · refine Or.inr ⟨fun h => hne (splitMapA_inj t h), pv t u, ⟨Sum.inl u, rfl⟩, ?_, ?_⟩
        · exact adj_of_wc_pv t u _ ((splitMapA_adj t (Sum.inl u) x).2 h1)
        · exact adj_of_wc_pv t u _ ((splitMapA_adj t (Sum.inl u) y).2 h2)

end skip
end split
end FatFlat.Dev.Emb
end

section
set_option autoImplicit false

namespace FatFlat.Dev.Obs1
open FatFlat.Dev.Emb FatFlat.Hereditary

/-- the biclique `K_{n,m}` maps injectively into `K_{n+m}` -/
def bipHom (n m : ℕ) : completeBipartiteGraph (Fin n) (Fin m) →g (⊤ : SimpleGraph (Fin (n + m))) where
  toFun := finSumFinEquiv
  map_rel' := by
    intro a b h
    simp only [SimpleGraph.top_adj]
    exact fun e => h.ne (finSumFinEquiv.injective e)

lemma bipHom_inj (n m : ℕ) : Function.Injective (bipHom n m) := finSumFinEquiv.injective

lemma cidx_exists (n : ℕ) :
    ∃ c : (⊤ : SimpleGraph (Fin n)).edgeSet → Fin (n.choose 2), Function.Injective c := by
  classical
  have h : Fintype.card (⊤ : SimpleGraph (Fin n)).edgeSet ≤ n.choose 2 := by
    have := SimpleGraph.card_edgeFinset_le_card_choose_two (G := (⊤ : SimpleGraph (Fin n)))
    simpa only [SimpleGraph.edgeFinset, Set.toFinset_card, Fintype.card_fin] using this
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (by simpa using h : Fintype.card (⊤ : SimpleGraph (Fin n)).edgeSet ≤
      Fintype.card (Fin (n.choose 2)))
  exact ⟨f, f.injective⟩

variable {W : Type} {H : SimpleGraph W}

/-- `J H → K(W, m)` with principal vertices on the left side. -/
def jHomL {m : ℕ} (c : H.edgeSet → Fin m) : J H →g completeBipartiteGraph W (Fin m) where
  toFun
    | Sum.inl u => Sum.inl u
    | Sum.inr ⟨e, _⟩ => Sum.inr (c e)
  map_rel' := by
    rintro (u | ⟨e, i⟩) (v | ⟨e', j⟩) h
    · exact absurd h (SD_adj_inl_inl _ _ _ _)
    · simp [completeBipartiteGraph_adj]
    · simp [completeBipartiteGraph_adj]
    · rw [SD_adj_inr_inr] at h
      have := i.isLt; have := j.isLt
      omega

lemma jHomL_inj {m : ℕ} (c : H.edgeSet → Fin m) (hc : Function.Injective c) :
    Function.Injective (jHomL c) := by
  rintro (u | ⟨e, i⟩) (v | ⟨e', j⟩) h
  · simpa [jHomL] using h
  · simp [jHomL] at h
  · simp [jHomL] at h
  · have h' : c e = c e' := by simpa [jHomL] using h
    have := hc h'
    subst this
    have : i = j := Fin.ext (by have := i.isLt; have := j.isLt; omega)
    rw [this]

/-- `J H → K(Fin m, W)` with principal vertices on the right side. -/
def jHomR {m : ℕ} (c : H.edgeSet → Fin m) : J H →g completeBipartiteGraph (Fin m) W where
  toFun
    | Sum.inl u => Sum.inr u
    | Sum.inr ⟨e, _⟩ => Sum.inl (c e)
  map_rel' := by
    rintro (u | ⟨e, i⟩) (v | ⟨e', j⟩) h
    · exact absurd h (SD_adj_inl_inl _ _ _ _)
    · simp [completeBipartiteGraph_adj]
    · simp [completeBipartiteGraph_adj]
    · rw [SD_adj_inr_inr] at h
      have := i.isLt; have := j.isLt
      omega

lemma jHomR_inj {m : ℕ} (c : H.edgeSet → Fin m) (hc : Function.Injective c) :
    Function.Injective (jHomR c) := by
  rintro (u | ⟨e, i⟩) (v | ⟨e', j⟩) h
  · simpa [jHomR] using h
  · simp [jHomR] at h
  · simp [jHomR] at h
  · have h' : c e = c e' := by simpa [jHomR] using h
    have := hc h'
    subst this
    have : i = j := Fin.ext (by have := i.isLt; have := j.isLt; omega)
    rw [this]

lemma splitM' (H : SimpleGraph W) (k t : ℕ) (hk : k = 2 * t + 2) :
    Nonempty (SD H k ↪g SD (J H) t) := by
  subst hk; exact ⟨splitEmbM H t⟩

lemma splitWeb' (H : SimpleGraph W) (k t : ℕ) (hk : k = 2 * t + 1) :
    Nonempty (webOf (SD H k) (Set.range Sum.inl) ↪g
      webOf (SD (J H) t) (Set.range Sum.inl)) := by
  subst hk; exact ⟨splitEmbWeb H t⟩

lemma splitA' (H : SimpleGraph W) (k t : ℕ) (hk : k = 2 * t + 1) :
    Nonempty (SD H k ↪g WC H t) := by
  subst hk; exact ⟨splitEmbA H t⟩

theorem item1 (r n m : ℕ) : Nonempty (subdividedBiclique r n m ↪g subdividedClique r (n + m)) :=
  ⟨sdEmb (bipHom n m) (bipHom_inj n m) (r - 1)⟩

theorem item2 (r n m : ℕ) : Nonempty (biweb r n m ↪g web r (n + m)) :=
  ⟨webSdEmb (bipHom n m) (bipHom_inj n m) (r - 1)⟩

theorem item3 (r n : ℕ) (hr : 1 ≤ r) :
    Nonempty (subdividedClique (2 * r + 1) n ↪g subdividedBiclique r n (n.choose 2)) := by
  obtain ⟨c, hc⟩ := cidx_exists n
  obtain ⟨E1⟩ := splitM' (⊤ : SimpleGraph (Fin n)) (2 * r + 1 - 1) (r - 1) (by omega)
  exact ⟨E1.trans (sdEmb (jHomL c) (jHomL_inj c hc) (r - 1))⟩

theorem item4 (r n : ℕ) (hr : 1 ≤ r) :
    Nonempty (web (2 * r) n ↪g biweb r n (n.choose 2)) := by
  obtain ⟨c, hc⟩ := cidx_exists n
  obtain ⟨E1⟩ := splitWeb' (⊤ : SimpleGraph (Fin n)) (2 * r - 1) (r - 1) (by omega)
  exact ⟨E1.trans (webSdEmb (jHomL c) (jHomL_inj c hc) (r - 1))⟩

theorem item5 (r n : ℕ) (hr : 1 ≤ r) :
    Nonempty (subdividedClique (2 * r) n ↪g mixweb r (n.choose 2) n) := by
  obtain ⟨c, hc⟩ := cidx_exists n
  obtain ⟨E1⟩ := splitA' (⊤ : SimpleGraph (Fin n)) (2 * r - 1) (r - 1) (by omega)
  have E2 : Nonempty (webOf (SD (J (⊤ : SimpleGraph (Fin n))) (r - 1))
      (Sum.inl '' Set.range (cv (⊤ : SimpleGraph (Fin n)))) ↪g
      webOf (SD (completeBipartiteGraph (Fin (n.choose 2)) (Fin n)) (r - 1))
        (Sum.inl '' Set.range (Sum.inl : Fin (n.choose 2) → Fin (n.choose 2) ⊕ Fin n))) :=
    ⟨webSdEmbGen (jHomR c) (jHomR_inj c hc) (r - 1) _ _ (by
      intro u
      rcases u with u | ⟨e, i⟩
      · simp [jHomR, cv]
      · have i0 : i = 0 := Fin.ext (by have := i.isLt; show i.val = 0; omega)
        subst i0
        simp [jHomR, cv])⟩
  have e1 : (Sum.inl '' Set.range (cv (⊤ : SimpleGraph (Fin n))) : Set _) =
      Set.range (mv (H := (⊤ : SimpleGraph (Fin n))) (r - 1)) := by
    ext x
    constructor
    · rintro ⟨_, ⟨e, rfl⟩, rfl⟩; exact ⟨e, rfl⟩
    · rintro ⟨e, rfl⟩; exact ⟨_, ⟨e, rfl⟩, rfl⟩
  have e2 : (Sum.inl '' Set.range (Sum.inl : Fin (n.choose 2) → Fin (n.choose 2) ⊕ Fin n) :
      Set ((Fin (n.choose 2) ⊕ Fin n) ⊕ (Σ _ : (completeBipartiteGraph (Fin (n.choose 2))
        (Fin n)).edgeSet, Fin (r - 1 + 1)))) =
      Set.range (fun i : Fin (n.choose 2) => (Sum.inl (Sum.inl i) :
        (Fin (n.choose 2) ⊕ Fin n) ⊕ (Σ _ : (completeBipartiteGraph (Fin (n.choose 2))
        (Fin n)).edgeSet, Fin (r - 1 + 1)))) := by
    ext x
    constructor
    · rintro ⟨_, ⟨e, rfl⟩, rfl⟩; exact ⟨e, rfl⟩
    · rintro ⟨e, rfl⟩; exact ⟨_, ⟨e, rfl⟩, rfl⟩
  rw [e1, e2] at E2
  obtain ⟨E2⟩ := E2
  exact ⟨E1.trans E2⟩

end FatFlat.Dev.Obs1

namespace FatFlat.Hereditary
open FatFlat.Dev.Obs1 in
theorem chk_observation_1 (r n m : ℕ) (hr : 3 ≤ r) :
    Nonempty (subdividedBiclique r n m ↪g subdividedClique r (n + m)) ∧
    Nonempty (biweb r n m ↪g web r (n + m)) ∧
    Nonempty (subdividedClique (2 * r + 1) n ↪g subdividedBiclique r n (n.choose 2)) ∧
    Nonempty (web (2 * r) n ↪g biweb r n (n.choose 2)) ∧
    Nonempty (subdividedClique (2 * r) n ↪g mixweb r (n.choose 2) n) :=
  ⟨item1 r n m, item2 r n m, item3 r n (by omega), item4 r n (by omega), item5 r n (by omega)⟩
end FatFlat.Hereditary
end

theorem solution : type_of% @FatFlat.Hereditary.chk_observation_1 := @FatFlat.Hereditary.chk_observation_1
