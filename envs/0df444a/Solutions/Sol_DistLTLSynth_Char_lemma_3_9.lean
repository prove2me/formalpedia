-- Prove2me | solution 1 for DistLTLSynth.Char.lemma_3_9
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T07:43:39.757178+00:00
-- url     : https://prove2.me/submissions/44e8c56a-41b3-47f4-abad-993e5335c2e9

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL
import Definitions.Def_DistLTLSynth_Char_Automata
import Definitions.Def_DistLTLSynth_Char_ComponentTree

namespace DistLTLSynth.Char.Lemma39Aux
open DistLTLSynth.Char

/-! ### Section 1: Views, depths, parent views, and block prefixes -/

def vdepth {X1 X2 : Type} : View X1 X2 → ℕ
  | .I1 => 0
  | .I2 => 0
  | .N1 _ u => vdepth u + 1
  | .N2 _ v => vdepth v + 1
  | .C1 _ u _ _ => vdepth u + 1
  | .C2 _ v _ _ => vdepth v + 1

def parentView {X1 X2 : Type} : View X1 X2 → View X1 X2
  | .I1 => .I1
  | .I2 => .I2
  | .N1 _ u => u
  | .N2 _ v => v
  | .C1 _ u _ _ => u
  | .C2 _ v _ _ => v

def iterParent {X1 X2 : Type} : ℕ → View X1 X2 → View X1 X2
  | 0, v => v
  | n + 1, v => iterParent n (parentView v)

lemma iterParent_succ_right {X1 X2 : Type} (n : ℕ) (v : View X1 X2) :
    parentView (iterParent n v) = iterParent n (parentView v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => exact ih (parentView v)

lemma views_append {X1 X2 : Type} (h u : List (Signal X1 X2)) :
    views (h ++ u) = u.foldl viewStep (views h) := by
  simp [views, List.foldl_append]

lemma vdepth_views {X1 X2 : Type} (h : List (Signal X1 X2)) :
    vdepth (view1 h) = h.length ∧ vdepth (view2 h) = h.length := by
  induction h using List.reverseRecOn with
  | nil => simp [view1, view2, views, vdepth]
  | append_singleton h a ih =>
    simp only [view1, view2] at ih ⊢
    rcases a with ⟨x1, x2, g⟩
    cases g <;> simp [views_append, viewStep, vdepth, ih.1, ih.2]

lemma parentView_view1_concat {X1 X2 : Type} (h : List (Signal X1 X2)) (a : Signal X1 X2) :
    parentView (view1 (h ++ [a])) = view1 h := by
  rcases a with ⟨x1, x2, g⟩
  cases g <;> simp [view1, views_append, viewStep, parentView]

lemma parentView_view2_concat {X1 X2 : Type} (h : List (Signal X1 X2)) (a : Signal X1 X2) :
    parentView (view2 (h ++ [a])) = view2 h := by
  rcases a with ⟨x1, x2, g⟩
  cases g <;> simp [view2, views_append, viewStep, parentView]

lemma iterParent_view1_append {X1 X2 : Type} (h u : List (Signal X1 X2)) :
    iterParent u.length (view1 (h ++ u)) = view1 h := by
  induction u using List.reverseRecOn with
  | nil => simp [iterParent]
  | append_singleton u a ih =>
    have hassoc : h ++ (u ++ [a]) = (h ++ u) ++ [a] := (List.append_assoc h u [a]).symm
    simp only [List.length_append, List.length_singleton, iterParent, hassoc,
      parentView_view1_concat]
    exact ih

lemma iterParent_view2_append {X1 X2 : Type} (h u : List (Signal X1 X2)) :
    iterParent u.length (view2 (h ++ u)) = view2 h := by
  induction u using List.reverseRecOn with
  | nil => simp [iterParent]
  | append_singleton u a ih =>
    have hassoc : h ++ (u ++ [a]) = (h ++ u) ++ [a] := (List.append_assoc h u [a]).symm
    simp only [List.length_append, List.length_singleton, iterParent, hassoc,
      parentView_view2_concat]
    exact ih

@[simp] lemma pre_length {α : Type} (w : ℕ → α) (r : ℕ) : (pre w r).length = r := by
  simp [pre]

lemma getElem_pre {α : Type} (w : ℕ → α) (r j : ℕ) (hj : j < (pre w r).length) :
    (pre w r)[j] = w j := by
  change (List.ofFn fun i : Fin r => w i.val)[j]'hj = w j
  exact List.getElem_ofFn _

lemma pre_add {α : Type} (w : ℕ → α) (m k : ℕ) :
    pre w (m + k) = pre w m ++ List.ofFn (fun i : Fin k => w (m + i.val)) := by
  apply List.ext_getElem
  · simp
  · intro j hj1 hj2
    rw [getElem_pre]
    by_cases hjm : j < m
    · rw [List.getElem_append_left (by simpa using hjm), getElem_pre]
    · have hge : m ≤ j := Nat.le_of_not_lt hjm
      rw [List.getElem_append_right (by simpa using hge), List.getElem_ofFn]
      simp [Nat.add_sub_of_le hge]

lemma ofFn_take_eq {α : Type} {D : ℕ} (u : Fin D → α) (m : ℕ) (hm : m ≤ D) :
    (List.ofFn u).take m = List.ofFn (fun j : Fin m => u ⟨j.val, Nat.lt_of_lt_of_le j.isLt hm⟩) := by
  apply List.ext_getElem
  · simp [hm]
  · intro j hj1 hj2
    simp

lemma append_inj_right_len {α : Type} {l1 r1 l2 r2 : List α}
    (heq : l1 ++ r1 = l2 ++ r2) (hlen : r1.length = r2.length) :
    l1 = l2 ∧ r1 = r2 := by
  have htot : l1.length + r1.length = l2.length + r2.length := by
    simpa [List.length_append] using congrArg List.length heq
  have hl : l1.length = l2.length := by omega
  exact List.append_inj heq hl

lemma ofFn_inj {α : Type} {n : ℕ} {f g : Fin n → α} (h : List.ofFn f = List.ofFn g) : f = g := by
  funext i
  have hi : i.val < (List.ofFn f).length := by simp [i.isLt]
  have hget := List.getElem_of_eq h hi
  simpa using hget

/-! ### Section 2: Lookup helpers, connected components, and uncompressed tree properties -/

lemma lookup_mem_of_exists {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {k : α}
    (h : ∃ v, (k, v) ∈ l) : ∃ v, l.lookup k = some v ∧ (k, v) ∈ l := by
  induction l with
  | nil =>
    rcases h with ⟨_, hm⟩
    cases hm
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    simp only [List.lookup]
    by_cases hkk : k = k'
    · subst hkk
      simp
    · have hbeq : (k == k') = false := beq_false_of_ne hkk
      rw [hbeq]
      rcases h with ⟨v, hv⟩
      rcases List.mem_cons.mp hv with heq | hmem
      · cases heq
        exact False.elim (hkk rfl)
      · rcases ih ⟨v, hmem⟩ with ⟨v0, hl, hm⟩
        exact ⟨v0, hl, List.mem_cons_of_mem _ hm⟩

lemma lookup_eq_of_unique {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {k : α} {v : β}
    (hex : ∃ w, (k, w) ∈ l) (huniq : ∀ w, (k, w) ∈ l → w = v) :
    l.lookup k = some v := by
  rcases lookup_mem_of_exists hex with ⟨w, hlk, hmem⟩
  rw [hlk, huniq w hmem]

def StepRel {X1 X2 : Type} (S : Set (List (Signal X1 X2))) (a b : List (Signal X1 X2)) : Prop :=
  a ∈ S ∧ b ∈ S ∧ EdgeAdj a b

lemma edgeAdj_symm {X1 X2 : Type} {a b : List (Signal X1 X2)} (h : EdgeAdj a b) : EdgeAdj b a := by
  rcases h with h1 | h2
  · exact Or.inl h1.symm
  · exact Or.inr h2.symm

lemma stepRel_symm {X1 X2 : Type} {S : Set (List (Signal X1 X2))} {a b : List (Signal X1 X2)}
    (h : StepRel S a b) : StepRel S b a :=
  ⟨h.2.1, h.1, edgeAdj_symm h.2.2⟩

lemma reflTransGen_stepRel_symm {X1 X2 : Type} {S : Set (List (Signal X1 X2))}
    {a b : List (Signal X1 X2)} (h : Relation.ReflTransGen (StepRel S) a b) :
    Relation.ReflTransGen (StepRel S) b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact (Relation.ReflTransGen.single (stepRel_symm hstep)).trans ih

lemma isComponentOf_subset {X1 X2 : Type} {S C : Set (List (Signal X1 X2))}
    (hC : IsComponentOf S C) : C ⊆ S := by
  rcases hC with ⟨c, hc, rfl⟩
  intro h hh
  cases hh with
  | refl => exact hc
  | tail _ hlast => exact hlast.2.1

lemma isComponentOf_closed {X1 X2 : Type} {S C : Set (List (Signal X1 X2))}
    {a b : List (Signal X1 X2)} (hC : IsComponentOf S C)
    (ha : a ∈ C) (hb : b ∈ S) (hadj : EdgeAdj a b) : b ∈ C := by
  have haS : a ∈ S := isComponentOf_subset hC ha
  rcases hC with ⟨c, _, rfl⟩
  exact Relation.ReflTransGen.tail ha ⟨haS, hb, hadj⟩

lemma isComponentOf_eq_of_inter {X1 X2 : Type} {S C1 C2 : Set (List (Signal X1 X2))}
    {h : List (Signal X1 X2)} (h1 : IsComponentOf S C1) (h2 : IsComponentOf S C2)
    (hm1 : h ∈ C1) (hm2 : h ∈ C2) : C1 = C2 := by
  rcases h1 with ⟨c1, _, rfl⟩
  rcases h2 with ⟨c2, _, rfl⟩
  have hc12 : Relation.ReflTransGen (StepRel S) c1 c2 :=
    hm1.trans (reflTransGen_stepRel_symm hm2)
  have hc21 : Relation.ReflTransGen (StepRel S) c2 c1 :=
    reflTransGen_stepRel_symm hc12
  ext x
  exact ⟨fun hx => hc21.trans hx, fun hx => hc12.trans hx⟩

lemma exists_componentOf_mem {X1 X2 : Type} {S : Set (List (Signal X1 X2))}
    {h : List (Signal X1 X2)} (hh : h ∈ S) :
    ∃ C, IsComponentOf S C ∧ h ∈ C :=
  ⟨{x | Relation.ReflTransGen (StepRel S) h x}, ⟨h, hh, rfl⟩, Relation.ReflTransGen.refl⟩

lemma valid_nil {L : Type} (t : LabeledTree L) : t.Valid [] := by
  intro i hi
  simp at hi

lemma valid_append_singleton_iff {L : Type} (t : LabeledTree L) (a : List ℕ) (i : ℕ) :
    t.Valid (a ++ [i]) ↔ t.Valid a ∧ i < t.nChildren a := by
  constructor
  · intro hv
    refine ⟨?_, ?_⟩
    · intro j hj
      have hj' : j < (a ++ [i]).length := by simp; omega
      have h := hv j hj'
      rwa [List.getElem_append_left hj, List.take_append_of_le_length (Nat.le_of_lt hj)] at h
    · have hj' : a.length < (a ++ [i]).length := by simp
      have h := hv a.length hj'
      simpa [List.take_append_of_le_length (le_refl a.length)] using h
  · rintro ⟨hva, hi⟩ j hj
    have hlen : (a ++ [i]).length = a.length + 1 := by simp
    by_cases hja : j < a.length
    · rw [List.getElem_append_left hja, List.take_append_of_le_length (Nat.le_of_lt hja)]
      exact hva j hja
    · have hjeq : j = a.length := by omega
      subst hjeq
      simpa [List.take_append_of_le_length (le_refl a.length)] using hi

lemma tree_edge_length {X1 X2 Y1 Y2 QB : Type} [DecidableEq X1] [DecidableEq X2]
    [Inhabited Y1] [Inhabited Y2] {D : ℕ}
    {B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))} {Qlive : Set QB}
    {t : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)}
    (ht : IsUncompressedComponentTree B Qlive t) :
    ∀ a, t.Valid a → ∀ e ∈ (t.label a).edges, e.length = a.length * D := by
  intro a
  induction a using List.reverseRecOn with
  | nil =>
    intro _ e he
    rw [ht.1] at he
    rw [Set.mem_singleton_iff.mp he]
    simp
  | append_singleton b i ih =>
    intro hv e he
    rcases (valid_append_singleton_iff t b i).mp hv with ⟨hvb, hi⟩
    have hcomp := ((ht.2.2 b hvb).2.1 i hi).1
    have he_live : e ∈ (t.label b).liveExt B Qlive := isComponentOf_subset hcomp he
    rcases he_live with ⟨p, hp, u, rfl, _⟩
    have hp_len := ih hvb p hp
    simp [hp_len, Nat.add_mul]

lemma valid_eq_of_edgeAdj {X1 X2 Y1 Y2 QB : Type} [DecidableEq X1] [DecidableEq X2]
    [Inhabited Y1] [Inhabited Y2] {D : ℕ}
    {B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))} {Qlive : Set QB}
    {t : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)}
    (ht : IsUncompressedComponentTree B Qlive t) :
    ∀ (k : ℕ) (a1 a2 : List ℕ), a1.length = k → a2.length = k →
      t.Valid a1 → t.Valid a2 →
      ∀ e1 ∈ (t.label a1).edges, ∀ e2 ∈ (t.label a2).edges, EdgeAdj e1 e2 → a1 = a2 := by
  intro k
  induction k with
  | zero =>
    intro a1 a2 h1 h2 _ _ _ _ _ _ _
    rw [List.eq_nil_of_length_eq_zero h1, List.eq_nil_of_length_eq_zero h2]
  | succ k ih =>
    intro a1 a2 h1 h2 hv1 hv2 e1 he1 e2 he2 hadj
    cases a1 using List.reverseRecOn with
    | nil => simp at h1
    | append_singleton b1 i1 =>
      cases a2 using List.reverseRecOn with
      | nil => simp at h2
      | append_singleton b2 i2 =>
        have hb1_len : b1.length = k := by simpa using h1
        have hb2_len : b2.length = k := by simpa using h2
        rcases (valid_append_singleton_iff t b1 i1).mp hv1 with ⟨hvb1, hi1⟩
        rcases (valid_append_singleton_iff t b2 i2).mp hv2 with ⟨hvb2, hi2⟩
        have hc1 := ((ht.2.2 b1 hvb1).2.1 i1 hi1).1
        have hc2 := ((ht.2.2 b2 hvb2).2.1 i2 hi2).1
        rcases isComponentOf_subset hc1 he1 with ⟨p1, hp1, u1, rfl, _⟩
        rcases isComponentOf_subset hc2 he2 with ⟨p2, hp2, u2, rfl, _⟩
        have hadj_p : EdgeAdj p1 p2 := by
          rcases hadj with hv | hv
          · left
            have hi_p1 := iterParent_view1_append p1 (List.ofFn u1)
            have hi_p2 := iterParent_view1_append p2 (List.ofFn u2)
            simp only [List.length_ofFn] at hi_p1 hi_p2
            rw [← hi_p1, ← hi_p2, hv]
          · right
            have hi_p1 := iterParent_view2_append p1 (List.ofFn u1)
            have hi_p2 := iterParent_view2_append p2 (List.ofFn u2)
            simp only [List.length_ofFn] at hi_p1 hi_p2
            rw [← hi_p1, ← hi_p2, hv]
        have hb_eq : b1 = b2 := ih b1 b2 hb1_len hb2_len hvb1 hvb2 p1 hp1 p2 hp2 hadj_p
        subst hb_eq
        have he2_in_c1 : p2 ++ List.ofFn u2 ∈ (t.label (b1 ++ [i1])).edges :=
          isComponentOf_closed hc1 he1 (isComponentOf_subset hc2 he2) hadj
        have hC_eq : (t.label (b1 ++ [i1])).edges = (t.label (b1 ++ [i2])).edges :=
          isComponentOf_eq_of_inter hc1 hc2 he2_in_c1 he2
        rcases (ht.2.2 b1 hvb1).2.2 (t.label (b1 ++ [i1])).edges hc1 with ⟨j, _, hj_uniq⟩
        have hj1 : i1 = j := hj_uniq i1 ⟨hi1, rfl⟩
        have hj2 : i2 = j := hj_uniq i2 ⟨hi2, hC_eq.symm⟩
        rw [hj1, hj2]

/-! ### Section 3: Deterministic readback from an accepting uncompressed tree -/

def validLevel {L : Type} (t : LabeledTree L) : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => (validLevel t k).flatMap fun a => (List.range (t.nChildren a)).map fun i => a ++ [i]

lemma mem_validLevel_iff {L : Type} (t : LabeledTree L) (k : ℕ) (a : List ℕ) :
    a ∈ validLevel t k ↔ a.length = k ∧ t.Valid a := by
  induction k generalizing a with
  | zero =>
    simp only [validLevel, List.mem_singleton, List.length_eq_zero_iff]
    exact ⟨fun h => ⟨h, h ▸ valid_nil t⟩, fun h => h.1⟩
  | succ k ih =>
    simp only [validLevel, List.mem_flatMap, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨b, hb, i, hi, rfl⟩
      rcases (ih b).mp hb with ⟨hlen, hvb⟩
      exact ⟨by simp [hlen], (valid_append_singleton_iff t b i).mpr ⟨hvb, hi⟩⟩
    · rintro ⟨hlen, hva⟩
      cases a using List.reverseRecOn with
      | nil => simp at hlen
      | append_singleton b i =>
        rcases (valid_append_singleton_iff t b i).mp hva with ⟨hvb, hi⟩
        exact ⟨b, (ih b).mpr ⟨by simpa using hlen, hvb⟩, i, hi, rfl⟩

def readback1 {X1 X2 Y1 Y2 QB : Type} [DecidableEq X1] [DecidableEq X2] [Inhabited Y1]
    (D : ℕ) (t : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)) (v : View X1 X2) : Y1 :=
  let d := vdepth v
  if d = 0 then default
  else
    let k := (d - 1) / D
    let r := (d - 1) % D + 1
    let vBase := iterParent r v
    match (validLevel t k).find? (fun a => (t.label a).1.any (fun p => view1 p.1 == vBase)) with
    | some a => (t.label a).lam1 v
    | none => default

def readback2 {X1 X2 Y1 Y2 QB : Type} [DecidableEq X1] [DecidableEq X2] [Inhabited Y2]
    (D : ℕ) (t : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)) (v : View X1 X2) : Y2 :=
  let d := vdepth v
  if d = 0 then default
  else
    let k := (d - 1) / D
    let r := (d - 1) % D + 1
    let vBase := iterParent r v
    match (validLevel t k).find? (fun a => (t.label a).1.any (fun p => view2 p.1 == vBase)) with
    | some a => (t.label a).lam2 v
    | none => default

def readbackAlgo {X1 X2 Y1 Y2 QB : Type} [DecidableEq X1] [DecidableEq X2]
    [Inhabited Y1] [Inhabited Y2] (D : ℕ)
    (t : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)) : Algorithm X1 X2 Y1 Y2 where
  f1 := readback1 D t
  f2 := readback2 D t

lemma readback1_eq_lam1 {X1 X2 Y1 Y2 QB : Type} [DecidableEq X1] [DecidableEq X2]
    [Inhabited Y1] [Inhabited Y2] {D : ℕ} (hD : 1 ≤ D)
    {B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))} {Qlive : Set QB}
    {t : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)}
    (ht : IsUncompressedComponentTree B Qlive t)
    {a : List ℕ} (hva : t.Valid a) {e : List (Signal X1 X2)} (he : e ∈ (t.label a).edges)
    {w : List (Signal X1 X2)} (hw1 : 1 ≤ w.length) (hwD : w.length ≤ D) :
    readback1 D t (view1 (e ++ w)) = (t.label a).lam1 (view1 (e ++ w)) := by
  have he_len : e.length = a.length * D := tree_edge_length ht a hva e he
  have hd : vdepth (view1 (e ++ w)) = a.length * D + w.length := by
    rw [(vdepth_views (e ++ w)).1, List.length_append, he_len]
  have hlen_ne : a.length * D + w.length ≠ 0 := by omega
  have hdiv : (a.length * D + w.length - 1) / D = a.length := by
    have hrew : a.length * D + w.length - 1 = (w.length - 1) + a.length * D := by omega
    rw [hrew, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]
  have hmod : (a.length * D + w.length - 1) % D + 1 = w.length := by
    have hrew : a.length * D + w.length - 1 = (w.length - 1) + a.length * D := by omega
    rw [hrew, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    omega
  unfold readback1
  simp only [hd, if_neg hlen_ne, hdiv, hmod, iterParent_view1_append]
  let pred : List ℕ → Bool := fun a' => (t.label a').1.any (fun p => view1 p.1 == view1 e)
  have ha_mem : a ∈ validLevel t a.length := (mem_validLevel_iff t a.length a).mpr ⟨rfl, hva⟩
  have ha_pred : pred a = true := by
    rcases he with ⟨s, hs⟩
    exact List.any_eq_true.mpr ⟨(e, s), hs, by simp⟩
  cases hfind : (validLevel t a.length).find? pred with
  | none =>
    have := (List.find?_eq_none.mp hfind) a ha_mem
    simp [ha_pred] at this
  | some a' =>
    have ha'_mem : a' ∈ validLevel t a.length := List.mem_of_find?_eq_some hfind
    have ha'_pred : pred a' = true := List.find?_some hfind
    rcases (mem_validLevel_iff t a.length a').mp ha'_mem with ⟨ha'_len, hva'⟩
    rcases List.any_eq_true.mp ha'_pred with ⟨⟨e', s'⟩, hs', hbeq⟩
    have hv_eq : view1 e' = view1 e := eq_of_beq hbeq
    have he' : e' ∈ (t.label a').edges := ⟨s', hs'⟩
    have ha_eq : a' = a :=
      valid_eq_of_edgeAdj ht a.length a' a ha'_len rfl hva' hva e' he' e he (Or.inl hv_eq)
    rw [ha_eq]

lemma readback2_eq_lam2 {X1 X2 Y1 Y2 QB : Type} [DecidableEq X1] [DecidableEq X2]
    [Inhabited Y1] [Inhabited Y2] {D : ℕ} (hD : 1 ≤ D)
    {B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))} {Qlive : Set QB}
    {t : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)}
    (ht : IsUncompressedComponentTree B Qlive t)
    {a : List ℕ} (hva : t.Valid a) {e : List (Signal X1 X2)} (he : e ∈ (t.label a).edges)
    {w : List (Signal X1 X2)} (hw1 : 1 ≤ w.length) (hwD : w.length ≤ D) :
    readback2 D t (view2 (e ++ w)) = (t.label a).lam2 (view2 (e ++ w)) := by
  have he_len : e.length = a.length * D := tree_edge_length ht a hva e he
  have hd : vdepth (view2 (e ++ w)) = a.length * D + w.length := by
    rw [(vdepth_views (e ++ w)).2, List.length_append, he_len]
  have hlen_ne : a.length * D + w.length ≠ 0 := by omega
  have hdiv : (a.length * D + w.length - 1) / D = a.length := by
    have hrew : a.length * D + w.length - 1 = (w.length - 1) + a.length * D := by omega
    rw [hrew, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega), zero_add]
  have hmod : (a.length * D + w.length - 1) % D + 1 = w.length := by
    have hrew : a.length * D + w.length - 1 = (w.length - 1) + a.length * D := by omega
    rw [hrew, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    omega
  unfold readback2
  simp only [hd, if_neg hlen_ne, hdiv, hmod, iterParent_view2_append]
  let pred : List ℕ → Bool := fun a' => (t.label a').1.any (fun p => view2 p.1 == view2 e)
  have ha_mem : a ∈ validLevel t a.length := (mem_validLevel_iff t a.length a).mpr ⟨rfl, hva⟩
  have ha_pred : pred a = true := by
    rcases he with ⟨s, hs⟩
    exact List.any_eq_true.mpr ⟨(e, s), hs, by simp⟩
  cases hfind : (validLevel t a.length).find? pred with
  | none =>
    have := (List.find?_eq_none.mp hfind) a ha_mem
    simp [ha_pred] at this
  | some a' =>
    have ha'_mem : a' ∈ validLevel t a.length := List.mem_of_find?_eq_some hfind
    have ha'_pred : pred a' = true := List.find?_some hfind
    rcases (mem_validLevel_iff t a.length a').mp ha'_mem with ⟨ha'_len, hva'⟩
    rcases List.any_eq_true.mp ha'_pred with ⟨⟨e', s'⟩, hs', hbeq⟩
    have hv_eq : view2 e' = view2 e := eq_of_beq hbeq
    have he' : e' ∈ (t.label a').edges := ⟨s', hs'⟩
    have ha_eq : a' = a :=
      valid_eq_of_edgeAdj ht a.length a' a ha'_len rfl hva' hva e' he' e he (Or.inr hv_eq)
    rw [ha_eq]

lemma readbackAlgo_realizes {X1 X2 Y1 Y2 QB : Type} [DecidableEq X1] [DecidableEq X2]
    [Inhabited Y1] [Inhabited Y2] {A : Set (ℕ → CommGraph)} {φ : Formula X1 X2 Y1 Y2}
    {D : ℕ} (hD : 1 ≤ D) {B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))} {Qlive : Set QB}
    (hB : IsBlockAutomaton A φ D B Qlive)
    {t : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)}
    (ht : IsUncompressedComponentTree B Qlive t) (hacc : IsAcceptingTree B t) :
    FRealizes (readbackAlgo D t) A φ := by
  classical
  intro h hg
  let f := readbackAlgo D t
  let uBlock : ℕ → Fin D → Signal X1 X2 := fun n i => h (n * D + i.val)
  have hpre_step : ∀ n, pre h ((n + 1) * D) = pre h (n * D) ++ List.ofFn (uBlock n) := by
    intro n
    rw [show (n + 1) * D = n * D + D from Nat.succ_mul n D]
    exact pre_add h (n * D) D
  have hreach : ∀ n : ℕ, ∃ a : List ℕ, a.length = n ∧ t.Valid a ∧
      pre h (n * D) ∈ (t.label a).edges ∧
      (t.label a).state B.init (pre h (n * D)) = B.run (toBlocks D (exec f h)) n := by
    intro n
    induction n with
    | zero =>
      refine ⟨[], rfl, valid_nil t, ?_, ?_⟩
      · rw [ht.1]; simp [pre]
      · rw [Nat.zero_mul]
        have hex : ∃ s, (pre h 0, s) ∈ (t.label []).1 := by
          change pre h 0 ∈ (t.label []).edges
          rw [ht.1]; simp [pre]
        have hlk := lookup_eq_of_unique hex (fun s hs => ht.2.1 _ s hs)
        unfold NodeLabel.state DPA.run
        rw [hlk]
        rfl
    | succ n ih =>
      rcases ih with ⟨a, ha_len, hva, he_mem, hstate⟩
      have hblock_eq : (fun i : Fin D => (uBlock n i,
          (t.label a).out (pre h (n * D)) ((List.ofFn (uBlock n)).take (i.val + 1)))) =
          toBlocks D (exec f h) n := by
        funext i
        let w := (List.ofFn (uBlock n)).take (i.val + 1)
        have hw_len : w.length = i.val + 1 := by simp [w, Nat.succ_le_of_lt i.isLt]
        have hw1 : 1 ≤ w.length := by omega
        have hwD : w.length ≤ D := by omega
        have hcat : pre h (n * D) ++ w = pre h (n * D + (i.val + 1)) := by
          dsimp only [w]
          rw [ofFn_take_eq (uBlock n) (i.val + 1) (Nat.succ_le_of_lt i.isLt)]
          exact (pre_add h (n * D) (i.val + 1)).symm
        have hf1 : f.f1 (view1 (pre h (n * D + i.val + 1))) =
            (t.label a).lam1 (view1 (pre h (n * D) ++ w)) := by
          change readback1 D t (view1 (pre h (n * D + (i.val + 1)))) = _
          rw [← hcat]
          exact readback1_eq_lam1 hD ht hva he_mem hw1 hwD
        have hf2 : f.f2 (view2 (pre h (n * D + i.val + 1))) =
            (t.label a).lam2 (view2 (pre h (n * D) ++ w)) := by
          change readback2 D t (view2 (pre h (n * D + (i.val + 1)))) = _
          rw [← hcat]
          exact readback2_eq_lam2 hD ht hva he_mem hw1 hwD
        simp only [toBlocks, exec, uBlock, NodeLabel.out]
        rw [hf1, hf2]
      have hqLam : (t.label a).qLam B (pre h (n * D)) (uBlock n) =
          B.run (toBlocks D (exec f h)) (n + 1) := by
        simp only [NodeLabel.qLam, DPA.run, hstate, hblock_eq]
      have hpref_live : pre (graphOfExec (exec f h)) ((n + 1) * D) ∈ Pref A := by
        refine ⟨graphOf h, hg, ?_⟩
        apply List.ext_getElem
        · simp
        · intro j hj1 hj2
          rw [getElem_pre, getElem_pre]
          rfl
      have hrun_live : B.run (toBlocks D (exec f h)) (n + 1) ∈ Qlive :=
        (hB.live (exec f h) (n + 1)).mpr hpref_live
      have he_next_live : pre h ((n + 1) * D) ∈ (t.label a).liveExt B Qlive :=
        ⟨pre h (n * D), he_mem, uBlock n, hpre_step n, hqLam ▸ hrun_live⟩
      rcases exists_componentOf_mem he_next_live with ⟨C, hC_comp, hC_mem⟩
      rcases (ht.2.2 a hva).2.2 C hC_comp with ⟨idx, ⟨hidx_lt, hidx_edges⟩, _⟩
      have hv_next : t.Valid (a ++ [idx]) := (valid_append_singleton_iff t a idx).mpr ⟨hva, hidx_lt⟩
      have he_next_mem : pre h ((n + 1) * D) ∈ (t.label (a ++ [idx])).edges := by
        rwa [hidx_edges]
      have hstate_next : (t.label (a ++ [idx])).state B.init (pre h ((n + 1) * D)) =
          B.run (toBlocks D (exec f h)) (n + 1) := by
        have huniq : ∀ s, (pre h ((n + 1) * D), s) ∈ (t.label (a ++ [idx])).1 →
            s = B.run (toBlocks D (exec f h)) (n + 1) := by
          intro s hs
          have hs_eq := ((ht.2.2 a hva).2.1 idx hidx_lt).2 _ s hs (pre h (n * D)) he_mem
            (uBlock n) (hpre_step n)
          exact hs_eq.trans hqLam
        have hlk := lookup_eq_of_unique he_next_mem huniq
        unfold NodeLabel.state
        rw [hlk]
        rfl
      exact ⟨a ++ [idx], by simp [ha_len], hv_next, he_next_mem, hstate_next⟩
  let aSeq : ℕ → List ℕ := fun n => (hreach n).choose
  have haSeq_spec : ∀ n, (aSeq n).length = n ∧ t.Valid (aSeq n) ∧
      pre h (n * D) ∈ (t.label (aSeq n)).edges ∧
      (t.label (aSeq n)).state B.init (pre h (n * D)) = B.run (toBlocks D (exec f h)) n :=
    fun n => (hreach n).choose_spec
  have ha0 : aSeq 0 = [] := List.eq_nil_of_length_eq_zero (haSeq_spec 0).1
  have ha_step : ∀ n, t.Valid (aSeq n) ∧ ∃ i, aSeq (n + 1) = aSeq n ++ [i] := by
    intro n
    refine ⟨(haSeq_spec n).2.1, ?_⟩
    have hlen1 : (aSeq (n + 1)).length = n + 1 := (haSeq_spec (n + 1)).1
    cases hcases : aSeq (n + 1) using List.reverseRecOn with
    | nil => simp [hcases] at hlen1
    | append_singleton b idx =>
      have hv_next : t.Valid (b ++ [idx]) := hcases ▸ (haSeq_spec (n + 1)).2.1
      rcases (valid_append_singleton_iff t b idx).mp hv_next with ⟨hvb, hidx⟩
      have hb_len : b.length = n := by
        have := congrArg List.length hcases
        simp [hlen1] at this
        omega
      have hc := ((ht.2.2 b hvb).2.1 idx hidx).1
      have he1_mem : pre h ((n + 1) * D) ∈ (t.label (b ++ [idx])).edges :=
        hcases ▸ (haSeq_spec (n + 1)).2.2.1
      rcases isComponentOf_subset hc he1_mem with ⟨p, hp, u', hp_eq, _⟩
      have hlen_u : (List.ofFn u').length = (List.ofFn (uBlock n)).length := by simp
      have hp_pre : p = pre h (n * D) :=
        (append_inj_right_len (hp_eq.symm.trans (hpre_step n)) hlen_u).1
      subst hp_pre
      have hb_eq : b = aSeq n :=
        valid_eq_of_edgeAdj ht n b (aSeq n) hb_len (haSeq_spec n).1 hvb (haSeq_spec n).2.1
          (pre h (n * D)) hp (pre h (n * D)) (haSeq_spec n).2.2.1 (Or.inl rfl)
      subst hb_eq
      exact ⟨idx, rfl⟩
  have hpar := hacc aSeq (fun n => pre h (n * D)) uBlock ha0 ha_step
    (by simp [pre]) hpre_step (fun n => (haSeq_spec n).2.2.1)
  have hpar' : B.Accepts (toBlocks D (exec f h)) := by
    unfold DPA.Accepts
    have hfn : (fun n => B.prio (B.run (toBlocks D (exec f h)) n)) =
        (fun n => B.prio ((t.label (aSeq n)).state B.init (pre h (n * D)))) := by
      funext n
      rw [(haSeq_spec n).2.2.2]
    rw [hfn]
    exact hpar
  rcases (hB.accepts (exec f h)).mp hpar' with hnotA | hsat
  · exact False.elim (hnotA hg)
  · exact hsat

/-! ### Section 4: Forward construction from a realizing algorithm -/

noncomputable section Forward

def allSubBlocks {X1 X2 : Type} [Fintype X1] [Fintype X2] [DecidableEq X1] [DecidableEq X2]
    (D : ℕ) : Finset (List (Signal X1 X2)) :=
  (Finset.Icc 1 D).biUnion fun m =>
    (Finset.univ : Finset (Fin m → Signal X1 X2)).image List.ofFn

lemma mem_allSubBlocks_iff {X1 X2 : Type} [Fintype X1] [Fintype X2]
    [DecidableEq X1] [DecidableEq X2] {D : ℕ} {u : List (Signal X1 X2)} :
    u ∈ allSubBlocks (X1 := X1) (X2 := X2) D ↔ 1 ≤ u.length ∧ u.length ≤ D := by
  simp only [allSubBlocks, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨m, ⟨hm1, hmD⟩, g, rfl⟩
    simp [hm1, hmD]
  · rintro ⟨hu1, huD⟩
    refine ⟨u.length, ⟨hu1, huD⟩, fun i => u[i.val], ?_⟩
    apply List.ext_getElem <;> simp

def mkNodeLabel {X1 X2 Y1 Y2 QB : Type} [Fintype X1] [Fintype X2]
    [DecidableEq X1] [DecidableEq X2] (D : ℕ) (f : Algorithm X1 X2 Y1 Y2)
    (E : Finset (List (Signal X1 X2))) (q : List (Signal X1 X2) → QB) :
    NodeLabel X1 X2 Y1 Y2 QB :=
  let V1 : Finset (View X1 X2) := (E ×ˢ allSubBlocks D).image fun p => view1 (p.1 ++ p.2)
  let V2 : Finset (View X1 X2) := (E ×ˢ allSubBlocks D).image fun p => view2 (p.1 ++ p.2)
  (E.toList.map (fun h => (h, q h)),
   V1.toList.map (fun v => (v, f.f1 v)),
   V2.toList.map (fun v => (v, f.f2 v)))

lemma mkNodeLabel_mem1 {X1 X2 Y1 Y2 QB : Type} [Fintype X1] [Fintype X2]
    [DecidableEq X1] [DecidableEq X2] {D : ℕ} {f : Algorithm X1 X2 Y1 Y2}
    {E : Finset (List (Signal X1 X2))} {q : List (Signal X1 X2) → QB}
    {h : List (Signal X1 X2)} {s : QB} :
    (h, s) ∈ (mkNodeLabel D f E q).1 ↔ h ∈ E ∧ s = q h := by
  simp only [mkNodeLabel, List.mem_map, Finset.mem_toList, Prod.mk.injEq]
  exact ⟨fun ⟨h', hh', heq1, heq2⟩ => ⟨heq1 ▸ hh', heq1 ▸ heq2.symm⟩,
    fun ⟨hh, hs⟩ => ⟨h, hh, rfl, hs.symm⟩⟩

lemma mkNodeLabel_edges {X1 X2 Y1 Y2 QB : Type} [Fintype X1] [Fintype X2]
    [DecidableEq X1] [DecidableEq X2] {D : ℕ} {f : Algorithm X1 X2 Y1 Y2}
    {E : Finset (List (Signal X1 X2))} {q : List (Signal X1 X2) → QB} :
    (mkNodeLabel D f E q).edges = (E : Set (List (Signal X1 X2))) := by
  ext h
  simp [NodeLabel.edges, mkNodeLabel_mem1]

lemma mkNodeLabel_covers {X1 X2 Y1 Y2 QB : Type} [Fintype X1] [Fintype X2]
    [DecidableEq X1] [DecidableEq X2] {D : ℕ} {f : Algorithm X1 X2 Y1 Y2}
    {E : Finset (List (Signal X1 X2))} {q : List (Signal X1 X2) → QB} :
    (mkNodeLabel D f E q).Covers D := by
  intro e he u hu1 huD
  rw [mkNodeLabel_edges] at he
  have hu : u ∈ allSubBlocks D := mem_allSubBlocks_iff.mpr ⟨hu1, huD⟩
  have hmem_prod : (e, u) ∈ E ×ˢ allSubBlocks D := Finset.mem_product.mpr ⟨he, hu⟩
  refine ⟨⟨f.f1 (view1 (e ++ u)), ?_⟩, ⟨f.f2 (view2 (e ++ u)), ?_⟩⟩
  · simp only [mkNodeLabel, List.mem_map, Finset.mem_toList, Finset.mem_image]
    exact ⟨view1 (e ++ u), ⟨(e, u), hmem_prod, rfl⟩, rfl⟩
  · simp only [mkNodeLabel, List.mem_map, Finset.mem_toList, Finset.mem_image]
    exact ⟨view2 (e ++ u), ⟨(e, u), hmem_prod, rfl⟩, rfl⟩

lemma mkNodeLabel_out {X1 X2 Y1 Y2 QB : Type} [Fintype X1] [Fintype X2]
    [DecidableEq X1] [DecidableEq X2] [Inhabited Y1] [Inhabited Y2]
    {D : ℕ} {f : Algorithm X1 X2 Y1 Y2}
    {E : Finset (List (Signal X1 X2))} {q : List (Signal X1 X2) → QB}
    {e : List (Signal X1 X2)} (he : e ∈ E) {w : List (Signal X1 X2)}
    (hw1 : 1 ≤ w.length) (hwD : w.length ≤ D) :
    (mkNodeLabel D f E q).out e w = (f.f1 (view1 (e ++ w)), f.f2 (view2 (e ++ w))) := by
  have hw : w ∈ allSubBlocks D := mem_allSubBlocks_iff.mpr ⟨hw1, hwD⟩
  have hmem_prod : (e, w) ∈ E ×ˢ allSubBlocks D := Finset.mem_product.mpr ⟨he, hw⟩
  have hlk1 : (mkNodeLabel D f E q).2.1.lookup (view1 (e ++ w)) = some (f.f1 (view1 (e ++ w))) := by
    apply lookup_eq_of_unique
    · refine ⟨f.f1 (view1 (e ++ w)), ?_⟩
      simp only [mkNodeLabel, List.mem_map, Finset.mem_toList, Finset.mem_image]
      exact ⟨view1 (e ++ w), ⟨(e, w), hmem_prod, rfl⟩, rfl⟩
    · intro y hy
      simp only [mkNodeLabel, List.mem_map, Finset.mem_toList, Prod.mk.injEq] at hy
      rcases hy with ⟨v', _, rfl, rfl⟩
      rfl
  have hlk2 : (mkNodeLabel D f E q).2.2.lookup (view2 (e ++ w)) = some (f.f2 (view2 (e ++ w))) := by
    apply lookup_eq_of_unique
    · refine ⟨f.f2 (view2 (e ++ w)), ?_⟩
      simp only [mkNodeLabel, List.mem_map, Finset.mem_toList, Finset.mem_image]
      exact ⟨view2 (e ++ w), ⟨(e, w), hmem_prod, rfl⟩, rfl⟩
    · intro y hy
      simp only [mkNodeLabel, List.mem_map, Finset.mem_toList, Prod.mk.injEq] at hy
      rcases hy with ⟨v', _, rfl, rfl⟩
      rfl
  simp [NodeLabel.out, NodeLabel.lam1, NodeLabel.lam2, hlk1, hlk2]

def liveExtFinset {X1 X2 Y1 Y2 QB : Type} [Fintype X1] [Fintype X2]
    [DecidableEq X1] [DecidableEq X2] [Inhabited Y1] [Inhabited Y2] {D : ℕ}
    (B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))) (Qlive : Set QB)
    (L : NodeLabel X1 X2 Y1 Y2 QB) (E : Finset (List (Signal X1 X2))) :
    Finset (List (Signal X1 X2)) :=
  (E ×ˢ (Finset.univ : Finset (Fin D → Signal X1 X2))).biUnion fun p =>
    @ite _ (L.qLam B p.1 p.2 ∈ Qlive) (Classical.propDecidable _) {p.1 ++ List.ofFn p.2} ∅

lemma coe_liveExtFinset {X1 X2 Y1 Y2 QB : Type} [Fintype X1] [Fintype X2]
    [DecidableEq X1] [DecidableEq X2] [Inhabited Y1] [Inhabited Y2] {D : ℕ}
    (B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))) (Qlive : Set QB)
    (f : Algorithm X1 X2 Y1 Y2) (E : Finset (List (Signal X1 X2)))
    (q : List (Signal X1 X2) → QB) :
    (liveExtFinset B Qlive (mkNodeLabel D f E q) E : Set (List (Signal X1 X2))) =
      (mkNodeLabel D f E q).liveExt B Qlive := by
  ext h
  simp only [liveExtFinset, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_product,
    Finset.mem_univ, and_true, NodeLabel.liveExt, mkNodeLabel_edges]
  change (∃ a : List (Signal X1 X2) × (Fin D → Signal X1 X2), a.1 ∈ E ∧
      h ∈ @ite _ ((mkNodeLabel D f E q).qLam B a.1 a.2 ∈ Qlive)
        (Classical.propDecidable _) {a.1 ++ List.ofFn a.2} ∅) ↔
    ∃ e ∈ (E : Set _), ∃ u, h = e ++ List.ofFn u ∧ (mkNodeLabel D f E q).qLam B e u ∈ Qlive
  constructor
  · rintro ⟨⟨e, u⟩, he, hh⟩
    by_cases hql : (mkNodeLabel D f E q).qLam B e u ∈ Qlive
    · rw [@if_pos _ (Classical.propDecidable _) hql] at hh
      exact ⟨e, he, u, Finset.mem_singleton.mp hh, hql⟩
    · rw [@if_neg _ (Classical.propDecidable _) hql] at hh
      exact False.elim (Finset.notMem_empty h hh)
  · rintro ⟨e, he, u, rfl, hql⟩
    refine ⟨(e, u), he, ?_⟩
    rw [@if_pos _ (Classical.propDecidable _) hql]
    exact Finset.mem_singleton_self _

def compsList {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (S_fin : Finset (List (Signal X1 X2))) : List (Finset (List (Signal X1 X2))) :=
  (@Finset.filter _ (fun C : Finset (List (Signal X1 X2)) =>
    IsComponentOf (S_fin : Set (List (Signal X1 X2))) (C : Set (List (Signal X1 X2))))
    (fun _ => Classical.propDecidable _) S_fin.powerset).toList

lemma compsList_nodup {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    (S_fin : Finset (List (Signal X1 X2))) : (compsList S_fin).Nodup :=
  Finset.nodup_toList _

lemma mem_compsList_iff {X1 X2 : Type} [DecidableEq X1] [DecidableEq X2]
    {S_fin C : Finset (List (Signal X1 X2))} :
    C ∈ compsList S_fin ↔
      IsComponentOf (S_fin : Set (List (Signal X1 X2))) (C : Set (List (Signal X1 X2))) := by
  simp only [compsList, Finset.mem_toList, @Finset.mem_filter _ _ (fun _ => Classical.propDecidable _),
    Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨Finset.coe_subset.mp (isComponentOf_subset h), h⟩⟩

def stepNodeData {X1 X2 Y1 Y2 QB : Type} [Fintype X1] [Fintype X2]
    [DecidableEq X1] [DecidableEq X2] [Inhabited Y1] [Inhabited Y2] (D : ℕ)
    (B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))) (Qlive : Set QB)
    (f : Algorithm X1 X2 Y1 Y2)
    (st : Finset (List (Signal X1 X2)) × (List (Signal X1 X2) → QB)) (i : ℕ) :
    Finset (List (Signal X1 X2)) × (List (Signal X1 X2) → QB) :=
  let L := mkNodeLabel D f st.1 st.2
  let cs := compsList (liveExtFinset B Qlive L st.1)
  let E' := if hi : i < cs.length then cs[i] else ∅
  let q' : List (Signal X1 X2) → QB := fun h =>
    @dite _ (∃ e ∈ st.1, ∃ u : Fin D → Signal X1 X2, h = e ++ List.ofFn u)
      (Classical.propDecidable _)
      (fun hne => L.qLam B hne.choose hne.choose_spec.2.choose)
      (fun _ => B.init)
  (E', q')

def nodeData {X1 X2 Y1 Y2 QB : Type} [Fintype X1] [Fintype X2]
    [DecidableEq X1] [DecidableEq X2] [Inhabited Y1] [Inhabited Y2] (D : ℕ)
    (B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))) (Qlive : Set QB)
    (f : Algorithm X1 X2 Y1 Y2) (a : List ℕ) :
    Finset (List (Signal X1 X2)) × (List (Signal X1 X2) → QB) :=
  a.foldl (stepNodeData D B Qlive f) ({[]}, fun _ => B.init)

def algoTree {X1 X2 Y1 Y2 QB : Type} [Fintype X1] [Fintype X2]
    [DecidableEq X1] [DecidableEq X2] [Inhabited Y1] [Inhabited Y2] (D : ℕ)
    (B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))) (Qlive : Set QB)
    (f : Algorithm X1 X2 Y1 Y2) : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB) where
  label a :=
    let st := nodeData D B Qlive f a
    mkNodeLabel D f st.1 st.2
  nChildren a :=
    let st := nodeData D B Qlive f a
    let L := mkNodeLabel D f st.1 st.2
    (compsList (liveExtFinset B Qlive L st.1)).length

lemma algoTree_uncompressed {X1 X2 Y1 Y2 QB : Type} [Fintype X1] [Fintype X2]
    [DecidableEq X1] [DecidableEq X2] [Inhabited Y1] [Inhabited Y2] (D : ℕ)
    (B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))) (Qlive : Set QB)
    (f : Algorithm X1 X2 Y1 Y2) :
    IsUncompressedComponentTree B Qlive (algoTree D B Qlive f) := by
  refine ⟨?_, ?_, ?_⟩
  · change (mkNodeLabel D f ({[]} : Finset _) _).edges = {[]}
    rw [mkNodeLabel_edges]
    simp
  · intro h s hs
    exact (mkNodeLabel_mem1.mp hs).2
  · intro a _
    let st := nodeData D B Qlive f a
    let L := mkNodeLabel D f st.1 st.2
    let S_fin := liveExtFinset B Qlive L st.1
    let cs := compsList S_fin
    have hlabel_a : (algoTree D B Qlive f).label a = L := rfl
    have hnchild_a : (algoTree D B Qlive f).nChildren a = cs.length := rfl
    have hS_coe : (S_fin : Set _) = L.liveExt B Qlive := coe_liveExtFinset B Qlive f st.1 st.2
    rw [hlabel_a, hnchild_a]
    refine ⟨mkNodeLabel_covers, ?_, ?_⟩
    · intro i hi
      have hnd_next : nodeData D B Qlive f (a ++ [i]) = stepNodeData D B Qlive f st i := by
        simp [nodeData, st]
      have hst1_next : (nodeData D B Qlive f (a ++ [i])).1 = cs[i] := by
        rw [hnd_next]
        exact dif_pos hi
      refine ⟨?_, ?_⟩
      · change IsComponentOf (L.liveExt B Qlive) (mkNodeLabel D f (nodeData D B Qlive f (a ++ [i])).1 _).edges
        rw [mkNodeLabel_edges, hst1_next, ← hS_coe]
        exact mem_compsList_iff.mp (List.getElem_mem hi)
      · intro h s hs e he u h_eq
        rw [mkNodeLabel_edges] at he
        have hs_eq : s = (nodeData D B Qlive f (a ++ [i])).2 h := (mkNodeLabel_mem1.mp hs).2
        rw [hs_eq, hnd_next]
        have hne : ∃ e' ∈ st.1, ∃ u' : Fin D → Signal X1 X2, h = e' ++ List.ofFn u' :=
          ⟨e, he, u, h_eq⟩
        change @dite _ (∃ e' ∈ st.1, ∃ u' : Fin D → Signal X1 X2, h = e' ++ List.ofFn u')
          (Classical.propDecidable _) _ _ = L.qLam B e u
        rw [@dif_pos _ (Classical.propDecidable _) hne]
        have h_eq' : h = hne.choose ++ List.ofFn hne.choose_spec.2.choose :=
          hne.choose_spec.2.choose_spec
        have hinj := append_inj_right_len (h_eq'.symm.trans h_eq) (by simp)
        have hu_eq : hne.choose_spec.2.choose = u := ofFn_inj hinj.2
        exact congrArg₂ (NodeLabel.qLam B L) hinj.1 hu_eq
    · intro C hC
      rw [← hS_coe] at hC
      let C_fin : Finset (List (Signal X1 X2)) :=
        @Finset.filter _ (· ∈ C) (fun _ => Classical.propDecidable _) S_fin
      have hC_sub : C ⊆ (S_fin : Set _) := isComponentOf_subset hC
      have hC_coe : (C_fin : Set _) = C := by
        ext x
        simp only [C_fin, Finset.mem_coe, @Finset.mem_filter _ _ (fun _ => Classical.propDecidable _)]
        exact ⟨fun hx => hx.2, fun hx => ⟨hC_sub hx, hx⟩⟩
      have hC_mem : C_fin ∈ cs := mem_compsList_iff.mpr (hC_coe ▸ hC)
      rcases List.mem_iff_getElem.mp hC_mem with ⟨idx, hidx_lt, hidx_eq⟩
      refine ⟨idx, ⟨hidx_lt, ?_⟩, ?_⟩
      · change (mkNodeLabel D f (nodeData D B Qlive f (a ++ [idx])).1 _).edges = C
        rw [mkNodeLabel_edges]
        have hnd_next : nodeData D B Qlive f (a ++ [idx]) = stepNodeData D B Qlive f st idx := by
          simp [nodeData, st]
        have hst1 : (nodeData D B Qlive f (a ++ [idx])).1 = cs[idx] := by
          rw [hnd_next]
          exact dif_pos hidx_lt
        rw [hst1, hidx_eq, hC_coe]
      · rintro j ⟨hj_lt, hj_edges⟩
        have hnd_j : nodeData D B Qlive f (a ++ [j]) = stepNodeData D B Qlive f st j := by
          simp [nodeData, st]
        have hstj : (nodeData D B Qlive f (a ++ [j])).1 = cs[j] := by
          rw [hnd_j]
          exact dif_pos hj_lt
        have hcj_coe : (cs[j] : Set _) = C := by
          change (mkNodeLabel D f (nodeData D B Qlive f (a ++ [j])).1 _).edges = C at hj_edges
          rwa [mkNodeLabel_edges, hstj] at hj_edges
        have hidx_coe : (cs[idx] : Set (List (Signal X1 X2))) = C := by
          rw [hidx_eq, hC_coe]
        have hcj_eq : cs[j] = cs[idx] := Finset.coe_inj.mp (hcj_coe.trans hidx_coe.symm)
        exact (List.Nodup.getElem_inj_iff (compsList_nodup S_fin)).mp hcj_eq

lemma algoTree_accepting {X1 X2 Y1 Y2 QB : Type} [Fintype X1] [Fintype X2]
    [DecidableEq X1] [DecidableEq X2] [Inhabited Y1] [Inhabited Y2]
    {A : Set (ℕ → CommGraph)} {φ : Formula X1 X2 Y1 Y2}
    {D : ℕ} (hD : 1 ≤ D) {B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))} {Qlive : Set QB}
    (hB : IsBlockAutomaton A φ D B Qlive)
    {f : Algorithm X1 X2 Y1 Y2} (hf : FRealizes f A φ) :
    IsAcceptingTree B (algoTree D B Qlive f) := by
  let t := algoTree D B Qlive f
  have ht := algoTree_uncompressed D B Qlive f
  intro aSeq eSeq uSeq ha0 ha_step he0 he_step he_mem
  have hD_pos : 0 < D := by omega
  let hInf : ℕ → Signal X1 X2 := fun m => uSeq (m / D) ⟨m % D, Nat.mod_lt m hD_pos⟩
  have he_pre : ∀ n, eSeq n = pre hInf (n * D) := by
    intro n
    induction n with
    | zero => simp [he0, pre]
    | succ n ih =>
      rw [he_step n, ih, show (n + 1) * D = n * D + D from Nat.succ_mul n D, pre_add]
      congr 1
      apply List.ext_getElem
      · simp
      · intro j hj1 hj2
        simp only [List.getElem_ofFn, hInf]
        have hdiv : (n * D + j) / D = n := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hD_pos, Nat.div_eq_of_lt (by simpa using hj1), zero_add]
        have hmod : (n * D + j) % D = j := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by simpa using hj1)]
        exact congrArg₂ uSeq hdiv.symm (Fin.ext hmod.symm)
  have hstate_run : ∀ n, (t.label (aSeq n)).state B.init (eSeq n) =
      B.run (toBlocks D (exec f hInf)) n := by
    intro n
    induction n with
    | zero =>
      have hex : ∃ s, (eSeq 0, s) ∈ (t.label (aSeq 0)).1 := he_mem 0
      rw [ha0] at hex ⊢
      have hlk := lookup_eq_of_unique hex (fun s hs => ht.2.1 _ s hs)
      unfold NodeLabel.state DPA.run
      rw [hlk]
      rfl
    | succ n ih =>
      rcases ha_step n with ⟨hva_n, idx, ha_succ⟩
      have hv_succ : t.Valid (aSeq n ++ [idx]) := ha_succ ▸ (ha_step (n + 1)).1
      have hidx_lt : idx < t.nChildren (aSeq n) :=
        ((valid_append_singleton_iff t (aSeq n) idx).mp hv_succ).2
      have huniq : ∀ s, (eSeq (n + 1), s) ∈ (t.label (aSeq (n + 1))).1 →
          s = (t.label (aSeq n)).qLam B (eSeq n) (uSeq n) := by
        intro s hs
        rw [ha_succ] at hs
        exact ((ht.2.2 (aSeq n) hva_n).2.1 idx hidx_lt).2 _ s hs (eSeq n) (he_mem n) (uSeq n) (he_step n)
      have hlk := lookup_eq_of_unique (he_mem (n + 1)) huniq
      have hstate_step : (t.label (aSeq (n + 1))).state B.init (eSeq (n + 1)) =
          (t.label (aSeq n)).qLam B (eSeq n) (uSeq n) := by
        unfold NodeLabel.state
        rw [hlk]
        rfl
      rw [hstate_step]
      simp only [NodeLabel.qLam, DPA.run, ih]
      congr 1
      funext j
      have he_in_st : eSeq n ∈ (nodeData D B Qlive f (aSeq n)).1 := by
        have := he_mem n
        change eSeq n ∈ (mkNodeLabel D f (nodeData D B Qlive f (aSeq n)).1 _).edges at this
        rwa [mkNodeLabel_edges] at this
      let w := (List.ofFn (uSeq n)).take (j.val + 1)
      have hw_len : w.length = j.val + 1 := by simp [w, Nat.succ_le_of_lt j.isLt]
      have hout : (t.label (aSeq n)).out (eSeq n) w =
          (f.f1 (view1 (eSeq n ++ w)), f.f2 (view2 (eSeq n ++ w))) :=
        mkNodeLabel_out he_in_st (by omega) (by omega)
      have hcat : eSeq n ++ w = pre hInf (n * D + j.val + 1) := by
        have hstep_pre : pre hInf (n * D + D) = eSeq n ++ List.ofFn (uSeq n) := by
          rw [show n * D + D = (n + 1) * D from (Nat.succ_mul n D).symm, ← he_pre (n + 1), he_step n]
        have h1 : (pre hInf (n * D + D)).take (n * D + j.val + 1) = pre hInf (n * D + j.val + 1) := by
          apply List.ext_getElem
          · simp
          · intro m hm1 hm2
            rw [List.getElem_take]
            have hm_lt : m < n * D + D := by
              have hm_lt' : m < n * D + j.val + 1 := by simpa using hm2
              have hj_lt : j.val < D := j.isLt
              omega
            have hm_lhs := getElem_pre hInf (n * D + D) m (by simpa using hm_lt)
            have hm_rhs := getElem_pre hInf (n * D + j.val + 1) m hm2
            exact hm_lhs.trans hm_rhs.symm
        have h2 : (eSeq n ++ List.ofFn (uSeq n)).take (n * D + j.val + 1) = eSeq n ++ w := by
          have he_len : (eSeq n).length = n * D := by simp [he_pre n]
          rw [show n * D + j.val + 1 = (eSeq n).length + (j.val + 1) by omega,
            List.take_append]
          simp [w]
        rw [← h1, hstep_pre, h2]
      have huj : uSeq n j = hInf (n * D + j.val) := by
        simp only [hInf]
        have hdiv : (n * D + j.val) / D = n := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hD_pos, Nat.div_eq_of_lt j.isLt, zero_add]
        have hmod : (n * D + j.val) % D = j.val := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]
        exact congrArg₂ uSeq hdiv.symm (Fin.ext hmod.symm)
      change (uSeq n j, (t.label (aSeq n)).out (eSeq n) w) = toBlocks D (exec f hInf) n j
      rw [hout, hcat, huj]
      rfl
  have hacc_B : B.Accepts (toBlocks D (exec f hInf)) := by
    apply (hB.accepts (exec f hInf)).mpr
    by_cases hg : graphOf hInf ∈ A
    · exact Or.inr (hf hInf hg)
    · exact Or.inl hg
  unfold DPA.Accepts at hacc_B
  have hfn : (fun n => B.prio ((t.label (aSeq n)).state B.init (eSeq n))) =
      (fun n => B.prio (B.run (toBlocks D (exec f hInf)) n)) := by
    funext n
    rw [hstate_run n]
  rw [hfn]
  exact hacc_B

end Forward

/-! ### Section 5: Effective extraction via `Nat.Partrec.Code` -/

def sNat (x : ℕ) : ℕ := Nat.pair 0 x + 1
def encI1 : ℕ := Nat.pair (sNat 0) 0
def encI2 : ℕ := Nat.pair (sNat 1) 0
def encN1 (ex1 eu : ℕ) : ℕ := Nat.pair (sNat 2) (Nat.pair (sNat ex1) (Nat.pair (eu + 1) 0))
def encN2 (ex2 ev : ℕ) : ℕ := Nat.pair (sNat 3) (Nat.pair (sNat ex2) (Nat.pair (ev + 1) 0))
def encC1 (ex1 eu ex2 ev : ℕ) : ℕ :=
  Nat.pair (sNat 4) (Nat.pair (sNat ex1) (Nat.pair (eu + 1) (Nat.pair (sNat ex2) (Nat.pair (ev + 1) 0))))
def encC2 (ex2 ev ex1 eu : ℕ) : ℕ :=
  Nat.pair (sNat 5) (Nat.pair (sNat ex2) (Nat.pair (ev + 1) (Nat.pair (sNat ex1) (Nat.pair (eu + 1) 0))))

lemma encode_view_I1 {X1 X2 : Type} [Encodable X1] [Encodable X2] :
    Encodable.encode (View.I1 : View X1 X2) = encI1 := rfl
lemma encode_view_I2 {X1 X2 : Type} [Encodable X1] [Encodable X2] :
    Encodable.encode (View.I2 : View X1 X2) = encI2 := rfl
lemma encode_view_N1 {X1 X2 : Type} [Encodable X1] [Encodable X2] (x1 : X1) (u : View X1 X2) :
    Encodable.encode (View.N1 x1 u) = encN1 (Encodable.encode x1) (Encodable.encode u) := rfl
lemma encode_view_N2 {X1 X2 : Type} [Encodable X1] [Encodable X2] (x2 : X2) (v : View X1 X2) :
    Encodable.encode (View.N2 x2 v) = encN2 (Encodable.encode x2) (Encodable.encode v) := rfl
lemma encode_view_C1 {X1 X2 : Type} [Encodable X1] [Encodable X2]
    (x1 : X1) (u : View X1 X2) (x2 : X2) (v : View X1 X2) :
    Encodable.encode (View.C1 x1 u x2 v) =
      encC1 (Encodable.encode x1) (Encodable.encode u) (Encodable.encode x2) (Encodable.encode v) := rfl
lemma encode_view_C2 {X1 X2 : Type} [Encodable X1] [Encodable X2]
    (x2 : X2) (v : View X1 X2) (x1 : X1) (u : View X1 X2) :
    Encodable.encode (View.C2 x2 v x1 u) =
      encC2 (Encodable.encode x2) (Encodable.encode v) (Encodable.encode x1) (Encodable.encode u) := rfl

lemma encode_prod_eq {α β : Type} [Encodable α] [Encodable β] (a : α) (b : β) :
    Encodable.encode (a, b) = Nat.pair (Encodable.encode a) (Encodable.encode b) := rfl

lemma encode_list_map {α : Type} [Encodable α] (l : List α) :
    Encodable.encode l = Encodable.encode (l.map Encodable.encode) := by
  induction l with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.map_cons, Encodable.encode_list_cons, ih, Encodable.encode_nat]

lemma primrec₂_natPair : Primrec₂ Nat.pair :=
  Primrec.encode

lemma primrec_sNat : Primrec sNat :=
  Primrec.succ.comp (primrec₂_natPair.comp (Primrec.const 0) Primrec.id)

lemma primrec_encN1 : Primrec₂ encN1 :=
  primrec₂_natPair.comp (Primrec.const (sNat 2))
    (primrec₂_natPair.comp (primrec_sNat.comp Primrec.fst)
      (primrec₂_natPair.comp (Primrec.succ.comp Primrec.snd) (Primrec.const 0)))

lemma primrec_encN2 : Primrec₂ encN2 :=
  primrec₂_natPair.comp (Primrec.const (sNat 3))
    (primrec₂_natPair.comp (primrec_sNat.comp Primrec.fst)
      (primrec₂_natPair.comp (Primrec.succ.comp Primrec.snd) (Primrec.const 0)))

lemma primrec_encC1 : Primrec fun p : (ℕ × ℕ) × (ℕ × ℕ) => encC1 p.1.1 p.1.2 p.2.1 p.2.2 :=
  primrec₂_natPair.comp (Primrec.const (sNat 4))
    (primrec₂_natPair.comp (primrec_sNat.comp (Primrec.fst.comp Primrec.fst))
      (primrec₂_natPair.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))
        (primrec₂_natPair.comp (primrec_sNat.comp (Primrec.fst.comp Primrec.snd))
          (primrec₂_natPair.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const 0)))))

lemma primrec_encC2 : Primrec fun p : (ℕ × ℕ) × (ℕ × ℕ) => encC2 p.1.1 p.1.2 p.2.1 p.2.2 :=
  primrec₂_natPair.comp (Primrec.const (sNat 5))
    (primrec₂_natPair.comp (primrec_sNat.comp (Primrec.fst.comp Primrec.fst))
      (primrec₂_natPair.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))
        (primrec₂_natPair.comp (primrec_sNat.comp (Primrec.fst.comp Primrec.snd))
          (primrec₂_natPair.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const 0)))))

def parentNat (n : ℕ) : ℕ :=
  if n.unpair.1 ≤ 2 then n else n.unpair.2.unpair.2.unpair.1 - 1

lemma primrec_parentNat : Primrec parentNat :=
  Primrec.ite (Primrec.nat_le.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 2))
    Primrec.id
    (Primrec.nat_sub.comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))))
      (Primrec.const 1))

lemma sNat_0_le : sNat 0 ≤ 2 := by decide
lemma sNat_1_le : sNat 1 ≤ 2 := by decide
lemma sNat_2_gt : ¬ sNat 2 ≤ 2 := by decide
lemma sNat_3_gt : ¬ sNat 3 ≤ 2 := by decide
lemma sNat_4_gt : ¬ sNat 4 ≤ 2 := by decide
lemma sNat_5_gt : ¬ sNat 5 ≤ 2 := by decide

lemma parentNat_encode {X1 X2 : Type} [Encodable X1] [Encodable X2] (v : View X1 X2) :
    parentNat (Encodable.encode v) = Encodable.encode (parentView v) := by
  cases v with
  | I1 =>
    rw [encode_view_I1, show parentView (View.I1 : View X1 X2) = View.I1 from rfl, encode_view_I1]
    unfold parentNat encI1
    rw [Nat.unpair_pair, if_pos sNat_0_le]
  | I2 =>
    rw [encode_view_I2, show parentView (View.I2 : View X1 X2) = View.I2 from rfl, encode_view_I2]
    unfold parentNat encI2
    rw [Nat.unpair_pair, if_pos sNat_1_le]
  | N1 x1 u =>
    rw [encode_view_N1]
    unfold parentNat encN1 parentView
    simp only [Nat.unpair_pair, if_neg sNat_2_gt, Nat.add_sub_cancel]
  | N2 x2 v =>
    rw [encode_view_N2]
    unfold parentNat encN2 parentView
    simp only [Nat.unpair_pair, if_neg sNat_3_gt, Nat.add_sub_cancel]
  | C1 x1 u x2 v =>
    rw [encode_view_C1]
    unfold parentNat encC1 parentView
    simp only [Nat.unpair_pair, if_neg sNat_4_gt, Nat.add_sub_cancel]
  | C2 x2 v x1 u =>
    rw [encode_view_C2]
    unfold parentNat encC2 parentView
    simp only [Nat.unpair_pair, if_neg sNat_5_gt, Nat.add_sub_cancel]

def iterNat {α : Type} (g : α → α) (m : ℕ) (x : α) : α :=
  (List.range m).foldl (fun acc _ => g acc) x

lemma iterNat_zero {α : Type} (g : α → α) (x : α) : iterNat g 0 x = x := rfl

lemma iterNat_succ {α : Type} (g : α → α) (m : ℕ) (x : α) :
    iterNat g (m + 1) x = g (iterNat g m x) := by
  simp [iterNat, List.range_succ]

lemma iterNat_comm {α : Type} (g : α → α) (m : ℕ) (x : α) :
    g (iterNat g m x) = iterNat g m (g x) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [iterNat_succ, iterNat_succ, ih]

def iterParentNat (r n : ℕ) : ℕ := iterNat parentNat r n

lemma primrec_iterParentNat : Primrec₂ iterParentNat :=
  Primrec.list_foldl (Primrec.list_range.comp Primrec.fst) Primrec.snd
    (primrec_parentNat.comp (Primrec.fst.comp Primrec.snd)).to₂

lemma iterParentNat_encode {X1 X2 : Type} [Encodable X1] [Encodable X2] (r : ℕ) (v : View X1 X2) :
    iterParentNat r (Encodable.encode v) = Encodable.encode (iterParent r v) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change iterNat parentNat (r + 1) (Encodable.encode v) = Encodable.encode (iterParent (r + 1) v)
    rw [iterNat_succ]
    change parentNat (iterParentNat r (Encodable.encode v)) = Encodable.encode (iterParent r (parentView v))
    rw [ih, parentNat_encode, iterParent_succ_right]

lemma vdepth_le_encode {X1 X2 : Type} [Encodable X1] [Encodable X2] (v : View X1 X2) :
    vdepth v ≤ Encodable.encode v := by
  induction v with
  | I1 => exact Nat.zero_le _
  | I2 => exact Nat.zero_le _
  | N1 x1 u ih =>
    rw [encode_view_N1]
    unfold vdepth encN1
    have h1 : Encodable.encode u + 1 ≤ Nat.pair (Encodable.encode u + 1) 0 := Nat.left_le_pair _ _
    have h2 : Nat.pair (Encodable.encode u + 1) 0 ≤
        Nat.pair (sNat (Encodable.encode x1)) (Nat.pair (Encodable.encode u + 1) 0) := Nat.right_le_pair _ _
    have h3 : Nat.pair (sNat (Encodable.encode x1)) (Nat.pair (Encodable.encode u + 1) 0) ≤
        Nat.pair (sNat 2) (Nat.pair (sNat (Encodable.encode x1)) (Nat.pair (Encodable.encode u + 1) 0)) :=
      Nat.right_le_pair _ _
    omega
  | N2 x2 v ih =>
    rw [encode_view_N2]
    unfold vdepth encN2
    have h1 : Encodable.encode v + 1 ≤ Nat.pair (Encodable.encode v + 1) 0 := Nat.left_le_pair _ _
    have h2 : Nat.pair (Encodable.encode v + 1) 0 ≤
        Nat.pair (sNat (Encodable.encode x2)) (Nat.pair (Encodable.encode v + 1) 0) := Nat.right_le_pair _ _
    have h3 : Nat.pair (sNat (Encodable.encode x2)) (Nat.pair (Encodable.encode v + 1) 0) ≤
        Nat.pair (sNat 3) (Nat.pair (sNat (Encodable.encode x2)) (Nat.pair (Encodable.encode v + 1) 0)) :=
      Nat.right_le_pair _ _
    omega
  | C1 x1 u x2 v ihu _ =>
    rw [encode_view_C1]
    unfold vdepth encC1
    have h1 : Encodable.encode u + 1 ≤
        Nat.pair (Encodable.encode u + 1) (Nat.pair (sNat (Encodable.encode x2)) (Nat.pair (Encodable.encode v + 1) 0)) :=
      Nat.left_le_pair _ _
    have h2 : Nat.pair (Encodable.encode u + 1) (Nat.pair (sNat (Encodable.encode x2)) (Nat.pair (Encodable.encode v + 1) 0)) ≤
        Nat.pair (sNat (Encodable.encode x1))
          (Nat.pair (Encodable.encode u + 1) (Nat.pair (sNat (Encodable.encode x2)) (Nat.pair (Encodable.encode v + 1) 0))) :=
      Nat.right_le_pair _ _
    have h3 : Nat.pair (sNat (Encodable.encode x1))
          (Nat.pair (Encodable.encode u + 1) (Nat.pair (sNat (Encodable.encode x2)) (Nat.pair (Encodable.encode v + 1) 0))) ≤
        encC1 (Encodable.encode x1) (Encodable.encode u) (Encodable.encode x2) (Encodable.encode v) :=
      Nat.right_le_pair _ _
    unfold encC1 at h3
    omega
  | C2 x2 v x1 u ihv _ =>
    rw [encode_view_C2]
    unfold vdepth encC2
    have h1 : Encodable.encode v + 1 ≤
        Nat.pair (Encodable.encode v + 1) (Nat.pair (sNat (Encodable.encode x1)) (Nat.pair (Encodable.encode u + 1) 0)) :=
      Nat.left_le_pair _ _
    have h2 : Nat.pair (Encodable.encode v + 1) (Nat.pair (sNat (Encodable.encode x1)) (Nat.pair (Encodable.encode u + 1) 0)) ≤
        Nat.pair (sNat (Encodable.encode x2))
          (Nat.pair (Encodable.encode v + 1) (Nat.pair (sNat (Encodable.encode x1)) (Nat.pair (Encodable.encode u + 1) 0))) :=
      Nat.right_le_pair _ _
    have h3 : Nat.pair (sNat (Encodable.encode x2))
          (Nat.pair (Encodable.encode v + 1) (Nat.pair (sNat (Encodable.encode x1)) (Nat.pair (Encodable.encode u + 1) 0))) ≤
        encC2 (Encodable.encode x2) (Encodable.encode v) (Encodable.encode x1) (Encodable.encode u) :=
      Nat.right_le_pair _ _
    unfold encC2 at h3
    omega

def depthStepNat (st : ℕ × ℕ) : ℕ × ℕ :=
  if st.1.unpair.1 ≤ 2 then st else (parentNat st.1, st.2 + 1)

lemma primrec_depthStepNat : Primrec depthStepNat :=
  Primrec.ite (Primrec.nat_le.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)) (Primrec.const 2))
    Primrec.id
    (Primrec.pair (primrec_parentNat.comp Primrec.fst) (Primrec.succ.comp Primrec.snd))

def vdepthNat (n : ℕ) : ℕ := (iterNat depthStepNat n (n, 0)).2

lemma primrec_vdepthNat : Primrec vdepthNat :=
  Primrec.snd.comp
    (Primrec.list_foldl Primrec.list_range (Primrec.pair Primrec.id (Primrec.const 0))
      (primrec_depthStepNat.comp (Primrec.fst.comp Primrec.snd)).to₂)

lemma iterNat_depthStepNat_encode {X1 X2 : Type} [Encodable X1] [Encodable X2]
    (v : View X1 X2) :
    ∀ (m d : ℕ), vdepth v ≤ m →
      (iterNat depthStepNat m (Encodable.encode v, d)).2 = d + vdepth v := by
  induction v with
  | I1 =>
    intro m d _
    have hfix : ∀ k, iterNat depthStepNat k (Encodable.encode (View.I1 : View X1 X2), d) =
        (Encodable.encode (View.I1 : View X1 X2), d) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [iterNat_succ, ih]
        unfold depthStepNat
        rw [encode_view_I1]
        unfold encI1
        simp only [Nat.unpair_pair, if_pos sNat_0_le]
    rw [hfix m]
    simp [vdepth]
  | I2 =>
    intro m d _
    have hfix : ∀ k, iterNat depthStepNat k (Encodable.encode (View.I2 : View X1 X2), d) =
        (Encodable.encode (View.I2 : View X1 X2), d) := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [iterNat_succ, ih]
        unfold depthStepNat
        rw [encode_view_I2]
        unfold encI2
        simp only [Nat.unpair_pair, if_pos sNat_1_le]
    rw [hfix m]
    simp [vdepth]
  | N1 x1 u ih =>
    intro m d hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [vdepth] at hm; omega⟩
    rw [iterNat_succ, iterNat_comm depthStepNat]
    have hstep : depthStepNat (Encodable.encode (View.N1 x1 u), d) = (Encodable.encode u, d + 1) := by
      have hp := parentNat_encode (View.N1 x1 u)
      simp only [parentView] at hp
      unfold depthStepNat
      have hgt : ¬ (Encodable.encode (View.N1 x1 u)).unpair.1 ≤ 2 := by
        rw [encode_view_N1]; unfold encN1; rw [Nat.unpair_pair]; exact sNat_2_gt
      rw [if_neg hgt, hp]
    rw [hstep, ih k (d + 1) (by simp [vdepth] at hm; omega)]
    simp [vdepth]; omega
  | N2 x2 v ih =>
    intro m d hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [vdepth] at hm; omega⟩
    rw [iterNat_succ, iterNat_comm depthStepNat]
    have hstep : depthStepNat (Encodable.encode (View.N2 x2 v), d) = (Encodable.encode v, d + 1) := by
      have hp := parentNat_encode (View.N2 x2 v)
      simp only [parentView] at hp
      unfold depthStepNat
      have hgt : ¬ (Encodable.encode (View.N2 x2 v)).unpair.1 ≤ 2 := by
        rw [encode_view_N2]; unfold encN2; rw [Nat.unpair_pair]; exact sNat_3_gt
      rw [if_neg hgt, hp]
    rw [hstep, ih k (d + 1) (by simp [vdepth] at hm; omega)]
    simp [vdepth]; omega
  | C1 x1 u x2 v ihu _ =>
    intro m d hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [vdepth] at hm; omega⟩
    rw [iterNat_succ, iterNat_comm depthStepNat]
    have hstep : depthStepNat (Encodable.encode (View.C1 x1 u x2 v), d) = (Encodable.encode u, d + 1) := by
      have hp := parentNat_encode (View.C1 x1 u x2 v)
      simp only [parentView] at hp
      unfold depthStepNat
      have hgt : ¬ (Encodable.encode (View.C1 x1 u x2 v)).unpair.1 ≤ 2 := by
        rw [encode_view_C1]; unfold encC1; rw [Nat.unpair_pair]; exact sNat_4_gt
      rw [if_neg hgt, hp]
    rw [hstep, ihu k (d + 1) (by simp [vdepth] at hm; omega)]
    simp [vdepth]; omega
  | C2 x2 v x1 u ihv _ =>
    intro m d hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [vdepth] at hm; omega⟩
    rw [iterNat_succ, iterNat_comm depthStepNat]
    have hstep : depthStepNat (Encodable.encode (View.C2 x2 v x1 u), d) = (Encodable.encode v, d + 1) := by
      have hp := parentNat_encode (View.C2 x2 v x1 u)
      simp only [parentView] at hp
      unfold depthStepNat
      have hgt : ¬ (Encodable.encode (View.C2 x2 v x1 u)).unpair.1 ≤ 2 := by
        rw [encode_view_C2]; unfold encC2; rw [Nat.unpair_pair]; exact sNat_5_gt
      rw [if_neg hgt, hp]
    rw [hstep, ihv k (d + 1) (by simp [vdepth] at hm; omega)]
    simp [vdepth]; omega

lemma vdepthNat_encode {X1 X2 : Type} [Encodable X1] [Encodable X2] (v : View X1 X2) :
    vdepthNat (Encodable.encode v) = vdepth v := by
  unfold vdepthNat
  simpa using iterNat_depthStepNat_encode v (Encodable.encode v) 0 (vdepth_le_encode v)

def decodeListNat (n : ℕ) : List ℕ := (Encodable.decode (α := List ℕ) n).getD []

lemma primrec_decodeListNat : Primrec decodeListNat :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

lemma decodeListNat_encode {α : Type} [Encodable α] (l : List α) :
    decodeListNat (Encodable.encode l) = l.map Encodable.encode := by
  unfold decodeListNat
  rw [encode_list_map, Encodable.encodek]
  rfl

attribute [local irreducible] encN1 encN2 encC1 encC2

def viewStepNatAux (g1 g2 : ℕ) (uv : ℕ × ℕ) (sigNum : ℕ) : ℕ × ℕ :=
  let ex1 := sigNum.unpair.1
  let ex2 := sigNum.unpair.2.unpair.1
  let eg := sigNum.unpair.2.unpair.2
  if eg = g1 then (encN1 ex1 uv.1, encC2 ex2 uv.2 ex1 uv.1)
  else if eg = g2 then (encC1 ex1 uv.1 ex2 uv.2, encC2 ex2 uv.2 ex1 uv.1)
  else (encC1 ex1 uv.1 ex2 uv.2, encN2 ex2 uv.2)

lemma primrec_viewStepNatAux (g1 g2 : ℕ) : Primrec₂ (viewStepNatAux g1 g2) := by
  have hex1 : Primrec fun p : (ℕ × ℕ) × ℕ => p.2.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hex2 : Primrec fun p : (ℕ × ℕ) × ℕ => p.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  have heg : Primrec fun p : (ℕ × ℕ) × ℕ => p.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  have huv1 : Primrec fun p : (ℕ × ℕ) × ℕ => p.1.1 := Primrec.fst.comp Primrec.fst
  have huv2 : Primrec fun p : (ℕ × ℕ) × ℕ => p.1.2 := Primrec.snd.comp Primrec.fst
  have hc1 : Primrec fun p : (ℕ × ℕ) × ℕ => encC1 p.2.unpair.1 p.1.1 p.2.unpair.2.unpair.1 p.1.2 :=
    primrec_encC1.comp (Primrec.pair (Primrec.pair hex1 huv1) (Primrec.pair hex2 huv2))
  have hc2 : Primrec fun p : (ℕ × ℕ) × ℕ => encC2 p.2.unpair.2.unpair.1 p.1.2 p.2.unpair.1 p.1.1 :=
    primrec_encC2.comp (Primrec.pair (Primrec.pair hex2 huv2) (Primrec.pair hex1 huv1))
  have hn1 : Primrec fun p : (ℕ × ℕ) × ℕ => encN1 p.2.unpair.1 p.1.1 := primrec_encN1.comp hex1 huv1
  have hn2 : Primrec fun p : (ℕ × ℕ) × ℕ => encN2 p.2.unpair.2.unpair.1 p.1.2 := primrec_encN2.comp hex2 huv2
  exact Primrec.ite (Primrec.eq.comp heg (Primrec.const g1))
    (Primrec.pair hn1 hc2)
    (Primrec.ite (Primrec.eq.comp heg (Primrec.const g2))
      (Primrec.pair hc1 hc2)
      (Primrec.pair hc1 hn2))

def viewStepNat : (ℕ × ℕ) → ℕ → (ℕ × ℕ) :=
  viewStepNatAux (Encodable.encode CommGraph.oneToTwo) (Encodable.encode CommGraph.both)

lemma primrec_viewStepNat : Primrec₂ viewStepNat :=
  primrec_viewStepNatAux _ _

lemma viewStepNat_encode {X1 X2 : Type} [Encodable X1] [Encodable X2]
    (uv : View X1 X2 × View X1 X2) (a : Signal X1 X2) :
    viewStepNat (Encodable.encode uv.1, Encodable.encode uv.2) (Encodable.encode a) =
      (Encodable.encode (viewStep uv a).1, Encodable.encode (viewStep uv a).2) := by
  rcases a with ⟨x1, x2, g⟩
  have ha : Encodable.encode (x1, x2, g) =
      Nat.pair (Encodable.encode x1) (Nat.pair (Encodable.encode x2) (Encodable.encode g)) := rfl
  have hne1 : Encodable.encode CommGraph.both ≠ Encodable.encode CommGraph.oneToTwo :=
    fun h => by cases Encodable.encode_injective h
  have hne2 : Encodable.encode CommGraph.twoToOne ≠ Encodable.encode CommGraph.oneToTwo :=
    fun h => by cases Encodable.encode_injective h
  have hne3 : Encodable.encode CommGraph.twoToOne ≠ Encodable.encode CommGraph.both :=
    fun h => by cases Encodable.encode_injective h
  rw [ha]
  unfold viewStepNat viewStepNatAux
  simp only [Nat.unpair_pair]
  cases g with
  | oneToTwo =>
    rw [if_pos rfl]
    simp only [viewStep, encode_view_N1, encode_view_C2]
  | both =>
    rw [if_neg hne1, if_pos rfl]
    simp only [viewStep, encode_view_C1, encode_view_C2]
  | twoToOne =>
    rw [if_neg hne2, if_neg hne3]
    simp only [viewStep, encode_view_C1, encode_view_N2]

def viewsNat (eh : ℕ) : ℕ × ℕ :=
  (decodeListNat eh).foldl viewStepNat (encI1, encI2)

lemma primrec_viewsNat : Primrec viewsNat :=
  Primrec.list_foldl primrec_decodeListNat (Primrec.const (encI1, encI2))
    (primrec_viewStepNat.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

lemma viewsNat_encode {X1 X2 : Type} [Encodable X1] [Encodable X2] (h : List (Signal X1 X2)) :
    viewsNat (Encodable.encode h) = (Encodable.encode (view1 h), Encodable.encode (view2 h)) := by
  unfold viewsNat
  rw [decodeListNat_encode]
  suffices ∀ uv : View X1 X2 × View X1 X2,
      (h.map Encodable.encode).foldl viewStepNat (Encodable.encode uv.1, Encodable.encode uv.2) =
        (Encodable.encode (h.foldl viewStep uv).1, Encodable.encode (h.foldl viewStep uv).2) by
    simpa [view1, view2, views, encode_view_I1, encode_view_I2] using this (View.I1, View.I2)
  induction h with
  | nil => intro uv; rfl
  | cons a tl ih =>
    intro uv
    simp only [List.map_cons, List.foldl_cons, viewStepNat_encode]
    exact ih (viewStep uv a)

def matchesNode1 (vBaseNum z : ℕ) : Bool :=
  (decodeListNat z.unpair.1.unpair.1).foldr
    (fun ep acc => if (viewsNat ep.unpair.1).1 = vBaseNum then true else acc) false

def matchesNode2 (vBaseNum z : ℕ) : Bool :=
  (decodeListNat z.unpair.1.unpair.1).foldr
    (fun ep acc => if (viewsNat ep.unpair.1).2 = vBaseNum then true else acc) false

lemma primrec_matchesNode1 : Primrec₂ matchesNode1 := by
  have hlist : Primrec fun p : ℕ × ℕ => decodeListNat p.2.unpair.1.unpair.1 :=
    primrec_decodeListNat.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))))
  have hv1 : Primrec fun q : (ℕ × ℕ) × (ℕ × Bool) => (viewsNat q.2.1.unpair.1).1 :=
    Primrec.fst.comp (primrec_viewsNat.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))))
  exact Primrec.list_foldr hlist (Primrec.const false)
    (Primrec.ite (Primrec.eq.comp hv1 (Primrec.fst.comp Primrec.fst))
      (Primrec.const true) (Primrec.snd.comp Primrec.snd)).to₂

lemma primrec_matchesNode2 : Primrec₂ matchesNode2 := by
  have hlist : Primrec fun p : ℕ × ℕ => decodeListNat p.2.unpair.1.unpair.1 :=
    primrec_decodeListNat.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))))
  have hv2 : Primrec fun q : (ℕ × ℕ) × (ℕ × Bool) => (viewsNat q.2.1.unpair.1).2 :=
    Primrec.snd.comp (primrec_viewsNat.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))))
  exact Primrec.list_foldr hlist (Primrec.const false)
    (Primrec.ite (Primrec.eq.comp hv2 (Primrec.fst.comp Primrec.fst))
      (Primrec.const true) (Primrec.snd.comp Primrec.snd)).to₂

lemma matchesNode1_encode {X1 X2 Y1 Y2 QB : Type} [DecidableEq X1] [DecidableEq X2]
    [Encodable X1] [Encodable X2] [Encodable Y1] [Encodable Y2] [Encodable QB]
    (vBase : View X1 X2) (L : NodeLabel X1 X2 Y1 Y2 QB) (nChild : ℕ) :
    matchesNode1 (Encodable.encode vBase) (Encodable.encode (L, nChild)) =
      L.1.any (fun p => view1 p.1 == vBase) := by
  have hz : (Encodable.encode (L, nChild)).unpair.1.unpair.1 = Encodable.encode L.1 := by
    rcases L with ⟨l1, l21, l22⟩
    simp [Nat.unpair_pair]
  unfold matchesNode1
  rw [hz, decodeListNat_encode]
  induction L.1 with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨e, s⟩
    simp only [List.map_cons, List.foldr_cons, encode_prod_eq, Nat.unpair_pair,
      viewsNat_encode, Encodable.encode_injective.eq_iff, List.any_cons, ih]
    by_cases heq : view1 e = vBase
    · simp [heq]
    · have hbeq : (view1 e == vBase) = false := beq_false_of_ne heq
      simp [heq, hbeq]

lemma matchesNode2_encode {X1 X2 Y1 Y2 QB : Type} [DecidableEq X1] [DecidableEq X2]
    [Encodable X1] [Encodable X2] [Encodable Y1] [Encodable Y2] [Encodable QB]
    (vBase : View X1 X2) (L : NodeLabel X1 X2 Y1 Y2 QB) (nChild : ℕ) :
    matchesNode2 (Encodable.encode vBase) (Encodable.encode (L, nChild)) =
      L.1.any (fun p => view2 p.1 == vBase) := by
  have hz : (Encodable.encode (L, nChild)).unpair.1.unpair.1 = Encodable.encode L.1 := by
    rcases L with ⟨l1, l21, l22⟩
    simp [Nat.unpair_pair]
  unfold matchesNode2
  rw [hz, decodeListNat_encode]
  induction L.1 with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨e, s⟩
    simp only [List.map_cons, List.foldr_cons, encode_prod_eq, Nat.unpair_pair,
      viewsNat_encode, Encodable.encode_injective.eq_iff, List.any_cons, ih]
    by_cases heq : view2 e = vBase
    · simp [heq]
    · have hbeq : (view2 e == vBase) = false := beq_false_of_ne heq
      simp [heq, hbeq]

def lookupAssocNat (defNum keyNum listNum : ℕ) : ℕ :=
  (decodeListNat listNum).foldr
    (fun m acc => if keyNum = m.unpair.1 then m.unpair.2 else acc) defNum

lemma primrec_lookupAssocNat (defNum : ℕ) : Primrec₂ (lookupAssocNat defNum) :=
  Primrec.list_foldr (primrec_decodeListNat.comp Primrec.snd) (Primrec.const defNum)
    (Primrec.ite
      (Primrec.eq.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂

lemma lookupAssocNat_encode {α β : Type} [DecidableEq α] [Encodable α] [Encodable β]
    (d : β) (k : α) (l : List (α × β)) :
    lookupAssocNat (Encodable.encode d) (Encodable.encode k) (Encodable.encode l) =
      Encodable.encode ((l.lookup k).getD d) := by
  unfold lookupAssocNat
  rw [decodeListNat_encode]
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k', y'⟩
    simp only [List.map_cons, List.foldr_cons, encode_prod_eq, Nat.unpair_pair,
      Encodable.encode_injective.eq_iff, List.lookup]
    by_cases hkk : k = k'
    · subst hkk; simp
    · have hbeq : (k == k') = false := beq_false_of_ne hkk
      simp [hkk, hbeq, ih]

def findZ1 (vBaseNum : ℕ) (lvl : List (List ℕ × ℕ)) : Option ℕ :=
  lvl.foldr (fun az acc => if matchesNode1 vBaseNum az.2 = true then some az.2 else acc) none

def findZ2 (vBaseNum : ℕ) (lvl : List (List ℕ × ℕ)) : Option ℕ :=
  lvl.foldr (fun az acc => if matchesNode2 vBaseNum az.2 = true then some az.2 else acc) none

lemma primrec_findZ1 : Primrec₂ findZ1 :=
  Primrec.list_foldr Primrec.snd (Primrec.const none)
    (Primrec.ite
      (Primrec.eq.comp
        (primrec_matchesNode1.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.const true))
      (Primrec.option_some.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂

lemma primrec_findZ2 : Primrec₂ findZ2 :=
  Primrec.list_foldr Primrec.snd (Primrec.const none)
    (Primrec.ite
      (Primrec.eq.comp
        (primrec_matchesNode2.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.const true))
      (Primrec.option_some.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂

lemma foldr_find_map {α β : Type} (f : α → β) (q : β → Bool) (l : List α) :
    (l.map f).foldr (fun b acc => if q b = true then some b else acc) none =
      (l.find? (fun a => q (f a))).map f := by
  induction l with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.map_cons, List.foldr_cons, List.find?_cons]
    cases hq : q (f a) <;> simp [ih]

def selectOutputNat (D defY1 defY2 inp lvlEnc : ℕ) : ℕ :=
  let procBit := inp.unpair.1
  let vNum := inp.unpair.2
  let d := vdepthNat vNum
  if d = 0 then
    if procBit = 0 then defY1 else defY2
  else
    let r := (d - 1) % D + 1
    let vBaseNum := iterParentNat r vNum
    let lvl := (Encodable.decode (α := List (List ℕ × ℕ)) lvlEnc).getD []
    if procBit = 0 then
      match findZ1 vBaseNum lvl with
      | some z => lookupAssocNat defY1 vNum z.unpair.1.unpair.2.unpair.1
      | none => defY1
    else
      match findZ2 vBaseNum lvl with
      | some z => lookupAssocNat defY2 vNum z.unpair.1.unpair.2.unpair.2
      | none => defY2

lemma primrec_selectOutputNat (D defY1 defY2 : ℕ) : Primrec₂ (selectOutputNat D defY1 defY2) := by
  have hproc : Primrec fun p : ℕ × ℕ => p.1.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have hv : Primrec fun p : ℕ × ℕ => p.1.unpair.2 := Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)
  have hd : Primrec fun p : ℕ × ℕ => vdepthNat p.1.unpair.2 := primrec_vdepthNat.comp hv
  have hr : Primrec fun p : ℕ × ℕ => (vdepthNat p.1.unpair.2 - 1) % D + 1 :=
    Primrec.succ.comp (Primrec.nat_mod.comp (Primrec.nat_sub.comp hd (Primrec.const 1)) (Primrec.const D))
  have hvBase : Primrec fun p : ℕ × ℕ => iterParentNat ((vdepthNat p.1.unpair.2 - 1) % D + 1) p.1.unpair.2 :=
    primrec_iterParentNat.comp hr hv
  have hlvl : Primrec fun p : ℕ × ℕ => (Encodable.decode (α := List (List ℕ × ℕ)) p.2).getD [] :=
    Primrec.option_getD.comp (Primrec.decode.comp Primrec.snd) (Primrec.const [])
  have hf1 : Primrec fun p : ℕ × ℕ => findZ1 (iterParentNat ((vdepthNat p.1.unpair.2 - 1) % D + 1) p.1.unpair.2)
      ((Encodable.decode (α := List (List ℕ × ℕ)) p.2).getD []) :=
    primrec_findZ1.comp hvBase hlvl
  have hf2 : Primrec fun p : ℕ × ℕ => findZ2 (iterParentNat ((vdepthNat p.1.unpair.2 - 1) % D + 1) p.1.unpair.2)
      ((Encodable.decode (α := List (List ℕ × ℕ)) p.2).getD []) :=
    primrec_findZ2.comp hvBase hlvl
  have hbranch1 : Primrec fun p : ℕ × ℕ =>
      match findZ1 (iterParentNat ((vdepthNat p.1.unpair.2 - 1) % D + 1) p.1.unpair.2)
          ((Encodable.decode (α := List (List ℕ × ℕ)) p.2).getD []) with
      | some z => lookupAssocNat defY1 p.1.unpair.2 z.unpair.1.unpair.2.unpair.1
      | none => defY1 := by
    have hbody : Primrec fun q : (ℕ × ℕ) × ℕ =>
        lookupAssocNat defY1 q.1.1.unpair.2 q.2.unpair.1.unpair.2.unpair.1 :=
      (primrec_lookupAssocNat defY1).comp (hv.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))))))
    exact (Primrec.option_casesOn hf1 (Primrec.const defY1) hbody.to₂).of_eq fun p => by
      cases findZ1 _ _ <;> rfl
  have hbranch2 : Primrec fun p : ℕ × ℕ =>
      match findZ2 (iterParentNat ((vdepthNat p.1.unpair.2 - 1) % D + 1) p.1.unpair.2)
          ((Encodable.decode (α := List (List ℕ × ℕ)) p.2).getD []) with
      | some z => lookupAssocNat defY2 p.1.unpair.2 z.unpair.1.unpair.2.unpair.2
      | none => defY2 := by
    have hbody : Primrec fun q : (ℕ × ℕ) × ℕ =>
        lookupAssocNat defY2 q.1.1.unpair.2 q.2.unpair.1.unpair.2.unpair.2 :=
      (primrec_lookupAssocNat defY2).comp (hv.comp Primrec.fst)
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))))))
    exact (Primrec.option_casesOn hf2 (Primrec.const defY2) hbody.to₂).of_eq fun p => by
      cases findZ2 _ _ <;> rfl
  exact Primrec.ite (Primrec.eq.comp hd (Primrec.const 0))
    (Primrec.ite (Primrec.eq.comp hproc (Primrec.const 0)) (Primrec.const defY1) (Primrec.const defY2))
    (Primrec.ite (Primrec.eq.comp hproc (Primrec.const 0)) hbranch1 hbranch2)

/-! #### Partial recursive BFS over valid tree levels -/

def evalAddrsStep (w : ℕ) : Part ℕ :=
  let a := w.unpair.1
  let y := w.unpair.2.unpair.1
  let accEnc := w.unpair.2.unpair.2
  let c := Denumerable.ofNat Nat.Partrec.Code a.unpair.1
  let addrs := (Encodable.decode (α := List (List ℕ)) a.unpair.2).getD []
  let addr := addrs.getD y []
  let acc := (Encodable.decode (α := List (List ℕ × ℕ)) accEnc).getD []
  (c.eval (Encodable.encode addr)).map fun z => Encodable.encode (acc ++ [(addr, z)])

lemma partrec_evalAddrsStep : Nat.Partrec evalAddrsStep := by
  apply Partrec.nat_iff.mp
  have hc : Computable fun w : ℕ => Denumerable.ofNat Nat.Partrec.Code w.unpair.1.unpair.1 :=
    (Computable.ofNat Nat.Partrec.Code).comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))).to_comp
  have haddrs : Primrec fun w : ℕ => (Encodable.decode (α := List (List ℕ)) w.unpair.1.unpair.2).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
      (Primrec.const [])
  have hy : Primrec fun w : ℕ => w.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have haddr : Primrec fun w : ℕ =>
      ((Encodable.decode (α := List (List ℕ)) w.unpair.1.unpair.2).getD []).getD w.unpair.2.unpair.1 [] :=
    (Primrec.list_getD []).comp haddrs hy
  have hacc : Primrec fun w : ℕ => (Encodable.decode (α := List (List ℕ × ℕ)) w.unpair.2.unpair.2).getD [] :=
    Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
      (Primrec.const [])
  have heval : Partrec fun w : ℕ =>
      (Denumerable.ofNat Nat.Partrec.Code w.unpair.1.unpair.1).eval
        (Encodable.encode (((Encodable.decode (α := List (List ℕ)) w.unpair.1.unpair.2).getD []).getD w.unpair.2.unpair.1 [])) :=
    Nat.Partrec.Code.eval_part.comp hc (Primrec.encode.comp haddr).to_comp
  have hpost : Primrec₂ fun (w z : ℕ) =>
      Encodable.encode (((Encodable.decode (α := List (List ℕ × ℕ)) w.unpair.2.unpair.2).getD []) ++
        [(((Encodable.decode (α := List (List ℕ)) w.unpair.1.unpair.2).getD []).getD w.unpair.2.unpair.1 [], z)]) :=
    Primrec.encode.comp
      (Primrec.list_append.comp (hacc.comp Primrec.fst)
        (Primrec.list_cons.comp
          (Primrec.pair (haddr.comp Primrec.fst) Primrec.snd)
          (Primrec.const [])))
  exact heval.map hpost.to_comp

def evalAddrsUnpaired : ℕ →. ℕ :=
  Nat.unpaired fun a m =>
    m.rec (Part.some (Encodable.encode ([] : List (List ℕ × ℕ)))) fun y IH => do
      let i ← IH
      evalAddrsStep (Nat.pair a (Nat.pair y i))

lemma partrec_evalAddrsUnpaired : Nat.Partrec evalAddrsUnpaired :=
  Nat.Partrec.prec
    (Partrec.nat_iff.mp (Computable.const (Encodable.encode ([] : List (List ℕ × ℕ)))).partrec)
    partrec_evalAddrsStep

lemma evalAddrsUnpaired_spec {X1 X2 Y1 Y2 QB : Type} [Encodable X1] [Encodable X2]
    [Encodable Y1] [Encodable Y2] [Encodable QB]
    {t : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)} {c : Nat.Partrec.Code}
    (hEff : EffectivelyGiven t c) (addrs : List (List ℕ)) (hValid : ∀ a ∈ addrs, t.Valid a) :
    ∀ m ≤ addrs.length,
      evalAddrsUnpaired (Nat.pair (Nat.pair (Encodable.encode c) (Encodable.encode addrs)) m) =
        Part.some (Encodable.encode ((addrs.take m).map fun a => (a, Encodable.encode (t.label a, t.nChildren a)))) := by
  intro m hm
  induction m with
  | zero =>
    simp [evalAddrsUnpaired, Nat.unpaired, Nat.unpair_pair]
  | succ y ih =>
    have hy_lt : y < addrs.length := by omega
    have ih_y := ih (Nat.le_of_lt hy_lt)
    simp only [evalAddrsUnpaired, Nat.unpaired, Nat.unpair_pair] at ih_y ⊢
    change Part.bind (Nat.rec _ _ y) (fun i => evalAddrsStep _) = _
    rw [ih_y, Part.bind_some]
    unfold evalAddrsStep
    simp only [Nat.unpair_pair, Denumerable.ofNat_encode, Encodable.encodek, Option.getD_some,
      List.getD_eq_getElem _ _ hy_lt]
    have hv_y : t.Valid addrs[y] := hValid addrs[y] (List.getElem_mem hy_lt)
    rw [hEff addrs[y] hv_y]
    simp only [Part.map_some]
    congr 2
    rw [List.take_add_one, List.getElem?_eq_getElem hy_lt, Option.toList_some, List.map_append, List.map_singleton]

def nextAddrsFromLvl (prevEnc : ℕ) : List (List ℕ) :=
  let prev := (Encodable.decode (α := List (List ℕ × ℕ)) prevEnc).getD []
  prev.flatMap fun az => (List.range az.2.unpair.2).map fun i => az.1 ++ [i]

lemma primrec_nextAddrsFromLvl : Primrec nextAddrsFromLvl := by
  have hprev : Primrec fun prevEnc : ℕ => (Encodable.decode (α := List (List ℕ × ℕ)) prevEnc).getD [] :=
    Primrec.option_getD.comp Primrec.decode (Primrec.const [])
  have hinner : Primrec fun q : ℕ × (List ℕ × ℕ) =>
      (List.range q.2.2.unpair.2).map fun i => q.2.1 ++ [i] :=
    Primrec.list_map
      (Primrec.list_range.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.list_append.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.list_cons.comp Primrec.snd (Primrec.const []))).to₂
  exact Primrec.list_flatMap hprev hinner.to₂

def bfsBase (cNum : ℕ) : Part ℕ :=
  evalAddrsUnpaired (Nat.pair (Nat.pair cNum (Encodable.encode ([[]] : List (List ℕ)))) 1)

def bfsStep (w : ℕ) : Part ℕ :=
  let cNum := w.unpair.1
  let prevEnc := w.unpair.2.unpair.2
  let addrs := nextAddrsFromLvl prevEnc
  evalAddrsUnpaired (Nat.pair (Nat.pair cNum (Encodable.encode addrs)) addrs.length)

lemma partrec_bfsBase : Nat.Partrec bfsBase := by
  apply Partrec.nat_iff.mp
  have harg : Primrec fun cNum : ℕ =>
      Nat.pair (Nat.pair cNum (Encodable.encode ([[]] : List (List ℕ)))) 1 :=
    primrec₂_natPair.comp
      (primrec₂_natPair.comp Primrec.id (Primrec.const (Encodable.encode ([[]] : List (List ℕ)))))
      (Primrec.const 1)
  exact (Partrec.nat_iff.mpr partrec_evalAddrsUnpaired).comp harg.to_comp

lemma partrec_bfsStep : Nat.Partrec bfsStep := by
  apply Partrec.nat_iff.mp
  have hcNum : Primrec fun w : ℕ => w.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hprev : Primrec fun w : ℕ => w.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have haddrs : Primrec fun w : ℕ => nextAddrsFromLvl w.unpair.2.unpair.2 :=
    primrec_nextAddrsFromLvl.comp hprev
  have harg : Primrec fun w : ℕ =>
      let addrs := nextAddrsFromLvl w.unpair.2.unpair.2
      Nat.pair (Nat.pair w.unpair.1 (Encodable.encode addrs)) addrs.length :=
    primrec₂_natPair.comp
      (primrec₂_natPair.comp hcNum (Primrec.encode.comp haddrs))
      (Primrec.list_length.comp haddrs)
  exact (Partrec.nat_iff.mpr partrec_evalAddrsUnpaired).comp harg.to_comp

def bfsLevelUnpaired : ℕ →. ℕ :=
  Nat.unpaired fun cNum k =>
    k.rec (bfsBase cNum) fun y IH => do
      let i ← IH
      bfsStep (Nat.pair cNum (Nat.pair y i))

lemma partrec_bfsLevelUnpaired : Nat.Partrec bfsLevelUnpaired :=
  Nat.Partrec.prec partrec_bfsBase partrec_bfsStep

lemma bfsLevelUnpaired_spec {X1 X2 Y1 Y2 QB : Type} [Encodable X1] [Encodable X2]
    [Encodable Y1] [Encodable Y2] [Encodable QB]
    {t : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)} {c : Nat.Partrec.Code}
    (hEff : EffectivelyGiven t c) (k : ℕ) :
    bfsLevelUnpaired (Nat.pair (Encodable.encode c) k) =
      Part.some (Encodable.encode ((validLevel t k).map fun a => (a, Encodable.encode (t.label a, t.nChildren a)))) := by
  induction k with
  | zero =>
    simp only [bfsLevelUnpaired, Nat.unpaired, Nat.unpair_pair, bfsBase]
    have hspec := evalAddrsUnpaired_spec hEff [[]]
      (fun a ha => by rw [List.mem_singleton.mp ha]; exact valid_nil t) 1 (by simp)
    simpa [validLevel] using hspec
  | succ y ih =>
    simp only [bfsLevelUnpaired, Nat.unpaired, Nat.unpair_pair] at ih ⊢
    change Part.bind (Nat.rec _ _ y) (fun i => bfsStep _) = _
    rw [ih, Part.bind_some]
    unfold bfsStep
    simp only [Nat.unpair_pair]
    have hnext : nextAddrsFromLvl
        (Encodable.encode ((validLevel t y).map fun a => (a, Encodable.encode (t.label a, t.nChildren a)))) =
        validLevel t (y + 1) := by
      unfold nextAddrsFromLvl
      rw [show validLevel t (y + 1) =
          (validLevel t y).flatMap (fun a => (List.range (t.nChildren a)).map fun i => a ++ [i]) from rfl]
      rw [Encodable.encodek, Option.getD_some, List.flatMap_map]
      congr 1
      funext a
      simp [Nat.unpair_pair]
    rw [hnext]
    have hvalid : ∀ a ∈ validLevel t (y + 1), t.Valid a :=
      fun a ha => ((mem_validLevel_iff t (y + 1) a).mp ha).2
    have hspec := evalAddrsUnpaired_spec hEff (validLevel t (y + 1)) hvalid
      (validLevel t (y + 1)).length (le_refl _)
    simpa [List.take_length] using hspec

def univReadback (D defY1 defY2 : ℕ) (z : ℕ) : Part ℕ :=
  let cNum := z.unpair.1
  let inp := z.unpair.2
  let vNum := inp.unpair.2
  let d := vdepthNat vNum
  if d = 0 then
    Part.some (selectOutputNat D defY1 defY2 inp 0)
  else
    let k := (d - 1) / D
    (bfsLevelUnpaired (Nat.pair cNum k)).map fun lvlEnc =>
      selectOutputNat D defY1 defY2 inp lvlEnc

lemma partrec_univReadback (D defY1 defY2 : ℕ) : Nat.Partrec (univReadback D defY1 defY2) := by
  apply Partrec.nat_iff.mp
  have hcNum : Primrec fun z : ℕ => z.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hinp : Primrec fun z : ℕ => z.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hvNum : Primrec fun z : ℕ => z.unpair.2.unpair.2 := Primrec.snd.comp (Primrec.unpair.comp hinp)
  have hd : Primrec fun z : ℕ => vdepthNat z.unpair.2.unpair.2 := primrec_vdepthNat.comp hvNum
  have hk : Primrec fun z : ℕ => (vdepthNat z.unpair.2.unpair.2 - 1) / D :=
    Primrec.nat_div.comp (Primrec.nat_sub.comp hd (Primrec.const 1)) (Primrec.const D)
  have hzeroBranch : Partrec fun z : ℕ => Part.some (selectOutputNat D defY1 defY2 z.unpair.2 0) :=
    ((primrec_selectOutputNat D defY1 defY2).comp hinp (Primrec.const 0)).to_comp.partrec
  have hbfs : Partrec fun z : ℕ => bfsLevelUnpaired (Nat.pair z.unpair.1 ((vdepthNat z.unpair.2.unpair.2 - 1) / D)) :=
    (Partrec.nat_iff.mpr partrec_bfsLevelUnpaired).comp (primrec₂_natPair.comp hcNum hk).to_comp
  have hposBranch : Partrec fun z : ℕ =>
      (bfsLevelUnpaired (Nat.pair z.unpair.1 ((vdepthNat z.unpair.2.unpair.2 - 1) / D))).map
        fun lvlEnc => selectOutputNat D defY1 defY2 z.unpair.2 lvlEnc :=
    hbfs.map ((primrec_selectOutputNat D defY1 defY2).comp (hinp.comp Primrec.fst) Primrec.snd).to_comp
  have hcond : Computable fun z : ℕ => decide (vdepthNat z.unpair.2.unpair.2 = 0) :=
    (Primrec.eq.comp hd (Primrec.const 0)).decide.to_comp
  exact (Partrec.cond hcond hzeroBranch hposBranch).of_eq fun z => by
    unfold univReadback
    by_cases h : vdepthNat z.unpair.2.unpair.2 = 0 <;> simp [h]

/-! #### Computability of `Nat.Partrec.Code.curry` -/

lemma encode_code_zero : Encodable.encode Nat.Partrec.Code.zero = 0 := rfl
lemma encode_code_succ : Encodable.encode Nat.Partrec.Code.succ = 1 := rfl
lemma encode_code_id : Encodable.encode Nat.Partrec.Code.id =
    Encodable.encode (Nat.Partrec.Code.pair .left .right) := rfl

lemma encode_code_pair (a b : Nat.Partrec.Code) :
    Encodable.encode (Nat.Partrec.Code.pair a b) =
      2 * (2 * Nat.pair (Encodable.encode a) (Encodable.encode b)) + 4 := rfl

lemma encode_code_comp (a b : Nat.Partrec.Code) :
    Encodable.encode (Nat.Partrec.Code.comp a b) =
      2 * (2 * Nat.pair (Encodable.encode a) (Encodable.encode b) + 1) + 4 := rfl

def encConstCode : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * (2 * Nat.pair 1 (encConstCode n) + 1) + 4

lemma encConstCode_eq (n : ℕ) : encConstCode n = Encodable.encode (Nat.Partrec.Code.const n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 2 * (2 * Nat.pair 1 (encConstCode n) + 1) + 4 =
      Encodable.encode (Nat.Partrec.Code.comp .succ (Nat.Partrec.Code.const n))
    rw [encode_code_comp, encode_code_succ, ih]

lemma primrec_encConstCode : Primrec encConstCode := by
  have hstep : Primrec fun p : ℕ × ℕ => 2 * (2 * Nat.pair 1 p.2 + 1) + 4 :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
          (primrec₂_natPair.comp (Primrec.const 1) Primrec.snd))))
      (Primrec.const 4)
  exact (Primrec.nat_rec₁ 0 hstep.to₂).of_eq fun n => by
    induction n with
    | zero => rfl
    | succ n ih => simp [encConstCode, ih]

lemma computable_curry (U : Nat.Partrec.Code) :
    Computable fun c : Nat.Partrec.Code => U.curry (Encodable.encode c) := by
  let eU := Encodable.encode U
  let eId := Encodable.encode Nat.Partrec.Code.id
  let encCurry : ℕ → ℕ := fun n =>
    let ePair := 2 * (2 * Nat.pair (encConstCode n) eId) + 4
    2 * (2 * Nat.pair eU ePair + 1) + 4
  have henc_prim : Primrec encCurry := by
    have hePair : Primrec fun n : ℕ => 2 * (2 * Nat.pair (encConstCode n) eId) + 4 :=
      Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.nat_mul.comp (Primrec.const 2)
            (primrec₂_natPair.comp primrec_encConstCode (Primrec.const eId))))
        (Primrec.const 4)
    exact Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
          (primrec₂_natPair.comp (Primrec.const eU) hePair))))
      (Primrec.const 4)
  have henc_eq : ∀ n, encCurry n = Encodable.encode (U.curry n) := by
    intro n
    dsimp only [encCurry, eU, eId]
    rw [encConstCode_eq]
    rfl
  have hcomp : Computable fun c : Nat.Partrec.Code =>
      Denumerable.ofNat Nat.Partrec.Code (encCurry (Encodable.encode c)) :=
    (Computable.ofNat Nat.Partrec.Code).comp (henc_prim.comp Primrec.encode).to_comp
  exact hcomp.of_eq fun c => by rw [henc_eq, Denumerable.ofNat_encode]

lemma exists_codeExtractor {X1 X2 Y1 Y2 QB : Type} [DecidableEq X1] [DecidableEq X2]
    [Encodable X1] [Encodable X2] [Inhabited Y1] [Encodable Y1] [Inhabited Y2] [Encodable Y2]
    [Encodable QB] {A : Set (ℕ → CommGraph)} {φ : Formula X1 X2 Y1 Y2}
    {D : ℕ} (hD : 1 ≤ D) {B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))} {Qlive : Set QB}
    (hB : IsBlockAutomaton A φ D B Qlive) :
    ∃ F : Nat.Partrec.Code → Nat.Partrec.Code, Computable F ∧
      ∀ (t : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)) (c : Nat.Partrec.Code),
        IsUncompressedComponentTree B Qlive t → IsAcceptingTree B t → EffectivelyGiven t c →
          ∃ f : Algorithm X1 X2 Y1 Y2, CodeComputes (F c) f ∧ FRealizes f A φ := by
  let defY1 := Encodable.encode (default : Y1)
  let defY2 := Encodable.encode (default : Y2)
  rcases Nat.Partrec.Code.exists_code.mp (partrec_univReadback D defY1 defY2) with ⟨U, hU⟩
  refine ⟨fun c => U.curry (Encodable.encode c), computable_curry U, ?_⟩
  intro t c ht hacc hEff
  refine ⟨readbackAlgo D t, ?_, readbackAlgo_realizes hD hB ht hacc⟩
  intro v
  have heval : ∀ b : ℕ, (U.curry (Encodable.encode c)).eval (Nat.pair b (Encodable.encode v)) =
      univReadback D defY1 defY2 (Nat.pair (Encodable.encode c) (Nat.pair b (Encodable.encode v))) := by
    intro b
    rw [Nat.Partrec.Code.eval_curry, hU]
  constructor
  · rw [heval 0]
    unfold univReadback
    simp only [Nat.unpair_pair, vdepthNat_encode]
    by_cases hd : vdepth v = 0
    · simp [hd, selectOutputNat, Nat.unpair_pair, vdepthNat_encode, readbackAlgo, readback1, defY1]
    · simp only [if_neg hd]
      rw [bfsLevelUnpaired_spec hEff ((vdepth v - 1) / D), Part.map_some]
      unfold selectOutputNat
      simp only [Nat.unpair_pair, vdepthNat_encode, if_neg hd, ↓reduceIte,
        iterParentNat_encode, Encodable.encodek, Option.getD_some]
      let k := (vdepth v - 1) / D
      let r := (vdepth v - 1) % D + 1
      let vBase := iterParent r v
      let fMap : List ℕ → List ℕ × ℕ := fun a => (a, Encodable.encode (t.label a, t.nChildren a))
      have hfind_eq : findZ1 (Encodable.encode vBase) ((validLevel t k).map fMap) =
          ((validLevel t k).find? fun a => (t.label a).1.any fun p => view1 p.1 == vBase).map
            fun a => Encodable.encode (t.label a, t.nChildren a) := by
        unfold findZ1
        have hmap_snd : ((validLevel t k).map fMap).foldr
            (fun az acc => if matchesNode1 (Encodable.encode vBase) az.2 = true then some az.2 else acc) none =
          (((validLevel t k).map fun a => Encodable.encode (t.label a, t.nChildren a)).foldr
            (fun z acc => if matchesNode1 (Encodable.encode vBase) z = true then some z else acc) none) := by
          induction validLevel t k with
          | nil => rfl
          | cons a tl ih =>
            simp only [List.map_cons, List.foldr_cons, ih]
            rfl
        rw [hmap_snd, foldr_find_map]
        congr 1
        apply List.find?_congr
        intro a _
        exact matchesNode1_encode vBase (t.label a) (t.nChildren a)
      congr 1
      rw [hfind_eq]
      unfold readbackAlgo readback1
      dsimp only
      rw [if_neg hd]
      cases hopt : (validLevel t k).find? fun a => (t.label a).1.any fun p => view1 p.1 == vBase with
      | none => rfl
      | some a =>
        simp only [Option.map_some]
        have hz21 : (Encodable.encode (t.label a, t.nChildren a)).unpair.1.unpair.2.unpair.1 =
            Encodable.encode (t.label a).2.1 := by
          rcases t.label a with ⟨l1, l21, l22⟩
          simp [Nat.unpair_pair]
        rw [hz21, lookupAssocNat_encode]
        rfl
  · rw [heval 1]
    unfold univReadback
    simp only [Nat.unpair_pair, vdepthNat_encode]
    by_cases hd : vdepth v = 0
    · simp [hd, selectOutputNat, Nat.unpair_pair, vdepthNat_encode, readbackAlgo, readback2, defY2]
    · simp only [if_neg hd]
      rw [bfsLevelUnpaired_spec hEff ((vdepth v - 1) / D), Part.map_some]
      unfold selectOutputNat
      simp only [Nat.unpair_pair, vdepthNat_encode, if_neg hd, one_ne_zero, ↓reduceIte,
        iterParentNat_encode, Encodable.encodek, Option.getD_some]
      let k := (vdepth v - 1) / D
      let r := (vdepth v - 1) % D + 1
      let vBase := iterParent r v
      let fMap : List ℕ → List ℕ × ℕ := fun a => (a, Encodable.encode (t.label a, t.nChildren a))
      have hfind_eq : findZ2 (Encodable.encode vBase) ((validLevel t k).map fMap) =
          ((validLevel t k).find? fun a => (t.label a).1.any fun p => view2 p.1 == vBase).map
            fun a => Encodable.encode (t.label a, t.nChildren a) := by
        unfold findZ2
        have hmap_snd : ((validLevel t k).map fMap).foldr
            (fun az acc => if matchesNode2 (Encodable.encode vBase) az.2 = true then some az.2 else acc) none =
          (((validLevel t k).map fun a => Encodable.encode (t.label a, t.nChildren a)).foldr
            (fun z acc => if matchesNode2 (Encodable.encode vBase) z = true then some z else acc) none) := by
          induction validLevel t k with
          | nil => rfl
          | cons a tl ih =>
            simp only [List.map_cons, List.foldr_cons, ih]
            rfl
        rw [hmap_snd, foldr_find_map]
        congr 1
        apply List.find?_congr
        intro a _
        exact matchesNode2_encode vBase (t.label a) (t.nChildren a)
      congr 1
      rw [hfind_eq]
      unfold readbackAlgo readback2
      dsimp only
      rw [if_neg hd]
      cases hopt : (validLevel t k).find? fun a => (t.label a).1.any fun p => view2 p.1 == vBase with
      | none => rfl
      | some a =>
        simp only [Option.map_some]
        have hz22 : (Encodable.encode (t.label a, t.nChildren a)).unpair.1.unpair.2.unpair.2 =
            Encodable.encode (t.label a).2.2 := by
          rcases t.label a with ⟨l1, l21, l22⟩
          simp [Nat.unpair_pair]
        rw [hz22, lookupAssocNat_encode]
        rfl

end DistLTLSynth.Char.Lemma39Aux

open DistLTLSynth.Char DistLTLSynth.Char.Lemma39Aux in
theorem solution {X1 X2 Y1 Y2 QB : Type} [Fintype X1] [Nonempty X1] [DecidableEq X1]
    [Encodable X1] [Fintype X2] [Nonempty X2] [DecidableEq X2] [Encodable X2]
    [Fintype Y1] [Inhabited Y1] [Encodable Y1] [Fintype Y2] [Inhabited Y2] [Encodable Y2]
    [Fintype QB] [Encodable QB]
    (A : Set (ℕ → CommGraph)) (φ : Formula X1 X2 Y1 Y2) (D : ℕ) (hD : 1 ≤ D)
    (B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))) (Qlive : Set QB)
    (hB : IsBlockAutomaton A φ D B Qlive) :
    ((∃ f : Algorithm X1 X2 Y1 Y2, FRealizes f A φ) ↔
        ∃ t : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB),
          IsUncompressedComponentTree B Qlive t ∧ IsAcceptingTree B t) ∧
      ∃ F : Nat.Partrec.Code → Nat.Partrec.Code, Computable F ∧
        ∀ (t : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)) (c : Nat.Partrec.Code),
          IsUncompressedComponentTree B Qlive t → IsAcceptingTree B t → EffectivelyGiven t c →
            ∃ f : Algorithm X1 X2 Y1 Y2, CodeComputes (F c) f ∧ FRealizes f A φ := by
  refine ⟨⟨?_, ?_⟩, exists_codeExtractor hD hB⟩
  · rintro ⟨f, hf⟩
    exact ⟨algoTree D B Qlive f, algoTree_uncompressed D B Qlive f, algoTree_accepting hD hB hf⟩
  · rintro ⟨t, ht, hacc⟩
    exact ⟨readbackAlgo D t, readbackAlgo_realizes hD hB ht hacc⟩
