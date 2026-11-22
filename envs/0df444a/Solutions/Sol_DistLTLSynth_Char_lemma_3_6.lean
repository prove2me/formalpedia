-- Prove2me | solution 1 for DistLTLSynth.Char.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T07:13:21.719009+00:00
-- url     : https://prove2.me/submissions/d61d7569-b137-4537-8945-e912a79c74a3

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_Geometric
import Definitions.Def_DistLTLSynth_Char_Automata
import Definitions.Def_DistLTLSynth_Char_Consensus
import Theorems.Thm_DistLTLSynth_Char_lemma_6_15

namespace DistLTLSynth.Char.Lemma36Aux
open DistLTLSynth.Char

/-! ### Geometric and view-coordinate helpers for the gap-table construction -/

def stepJ (a : ℕ) (g : CommGraph) : ℕ :=
  3 * a + if a % 2 = 0 then delta g else 2 - delta g

lemma delta_le (g : CommGraph) : delta g ≤ 2 := by
  cases g <;> simp [delta]

lemma delta_inj {x y : CommGraph} (h : delta x = delta y) : x = y := by
  cases x <;> cases y <;> simp_all [delta]

lemma stepJ_bounds (a : ℕ) (g : CommGraph) : 3 * a ≤ stepJ a g ∧ stepJ a g ≤ 3 * a + 2 := by
  have := delta_le g
  unfold stepJ
  split <;> omega

lemma jIdx_append (h : List CommGraph) (g : CommGraph) :
    jIdx (h ++ [g]) = stepJ (jIdx h) g := by
  unfold jIdx stepJ
  rw [List.foldl_append]
  rfl

lemma jIdx_lt (gs : List CommGraph) : jIdx gs < 3 ^ gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [jIdx]
  | append_singleton gs g ih =>
    rw [jIdx_append, List.length_append, List.length_singleton, pow_succ]
    have := stepJ_bounds (jIdx gs) g
    omega

lemma pre_succ_gen {α : Type} (w : ℕ → α) (r : ℕ) : pre w (r + 1) = pre w r ++ [w r] := by
  unfold pre
  rw [List.ofFn_succ', List.concat_eq_append]
  simp

lemma pre_length_gen {α : Type} (w : ℕ → α) (r : ℕ) : (pre w r).length = r := by
  simp [pre]

lemma extend_graphs (h : List CommGraph) : ∃ w : ℕ → CommGraph, pre w h.length = h := by
  refine ⟨fun i => h.getD i .both, ?_⟩
  apply List.ext_getElem
  · simp [pre]
  · intro i h1 h2; simp [pre]

lemma inj_pre : ∀ (m : ℕ) (w w' : ℕ → CommGraph),
    jIdx (pre w m) = jIdx (pre w' m) → pre w m = pre w' m
  | 0, _, _, _ => by simp [pre]
  | m + 1, w, w', h => by
      rw [pre_succ_gen, pre_succ_gen] at h ⊢
      rw [jIdx_append, jIdx_append] at h
      have b1 := stepJ_bounds (jIdx (pre w m)) (w m)
      have b2 := stepJ_bounds (jIdx (pre w' m)) (w' m)
      have ha : jIdx (pre w m) = jIdx (pre w' m) := by omega
      have hp := inj_pre m w w' ha
      rw [hp]
      congr 2
      rw [ha] at h
      apply delta_inj
      have d1 := delta_le (w m)
      have d2 := delta_le (w' m)
      unfold stepJ at h
      split at h <;> omega

lemma inj_list (g g' : List CommGraph) (hl : g.length = g'.length) (h : jIdx g = jIdx g') :
    g = g' := by
  obtain ⟨w, hw⟩ := extend_graphs g
  obtain ⟨w', hw'⟩ := extend_graphs g'
  rw [← hl] at hw'
  rw [← hw, ← hw'] at h ⊢
  exact inj_pre _ w w' h

def vround {X1 X2 : Type} : View X1 X2 → ℕ
  | .I1 => 0
  | .I2 => 0
  | .N1 _ u => vround u + 1
  | .N2 _ v => vround v + 1
  | .C1 _ u _ _ => vround u + 1
  | .C2 _ v _ _ => vround v + 1

def vprev {X1 X2 : Type} : View X1 X2 → View X1 X2
  | .I1 => .I1
  | .I2 => .I2
  | .N1 _ u => u
  | .N2 _ v => v
  | .C1 _ u _ _ => u
  | .C2 _ v _ _ => v

def viterPrev {X1 X2 : Type} : ℕ → View X1 X2 → View X1 X2
  | 0, v => v
  | k + 1, v => viterPrev k (vprev v)

def ancestorAt {X1 X2 : Type} (M : ℕ) (v : View X1 X2) : View X1 X2 :=
  viterPrev (vround v - M) v

def vcoord {X1 X2 : Type} : View X1 X2 → ℕ
  | .I1 => 0
  | .I2 => 1
  | .N1 _ u => 3 * vcoord u
  | .N2 _ v => 3 * vcoord v
  | .C1 _ u _ v => vcoord u + 2 * vcoord v
  | .C2 _ v _ u => vcoord v + 2 * vcoord u

lemma vround_views {X1 X2 : Type} (l : List (Signal X1 X2)) :
    vround (view1 l) = l.length ∧ vround (view2 l) = l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [view1, view2, views, vround]
  | append_singleton l s ih =>
    rcases s with ⟨x1, x2, g⟩
    have h1 : view1 (l ++ [(x1, x2, g)]) = (viewStep (view1 l, view2 l) (x1, x2, g)).1 := by
      simp [view1, view2, views]
    have h2 : view2 (l ++ [(x1, x2, g)]) = (viewStep (view1 l, view2 l) (x1, x2, g)).2 := by
      simp [view1, view2, views]
    rw [h1, h2]
    cases g <;> simp [viewStep, vround, ih.1, ih.2]

lemma vprev_pre {X1 X2 : Type} (h : ℕ → Signal X1 X2) (r : ℕ) :
    vprev (view1 (pre h (r + 1))) = view1 (pre h r) ∧
      vprev (view2 (pre h (r + 1))) = view2 (pre h r) := by
  rw [pre_succ_gen]
  rcases h r with ⟨x1, x2, g⟩
  have h1 : view1 (pre h r ++ [(x1, x2, g)]) =
      (viewStep (view1 (pre h r), view2 (pre h r)) (x1, x2, g)).1 := by
    simp [view1, view2, views]
  have h2 : view2 (pre h r ++ [(x1, x2, g)]) =
      (viewStep (view1 (pre h r), view2 (pre h r)) (x1, x2, g)).2 := by
    simp [view1, view2, views]
  rw [h1, h2]
  cases g <;> simp [viewStep, vprev]

lemma viterPrev_pre {X1 X2 : Type} (h : ℕ → Signal X1 X2) (M : ℕ) :
    ∀ d : ℕ,
      viterPrev d (view1 (pre h (M + d))) = view1 (pre h M) ∧
      viterPrev d (view2 (pre h (M + d))) = view2 (pre h M)
  | 0 => ⟨rfl, rfl⟩
  | d + 1 => by
      have heq : M + (d + 1) = M + d + 1 := by omega
      have hp := vprev_pre h (M + d)
      have ih := viterPrev_pre h M d
      exact ⟨by rw [viterPrev, heq, hp.1, ih.1],
             by rw [viterPrev, heq, hp.2, ih.2]⟩

lemma ancestorAt_pre {X1 X2 : Type} (h : ℕ → Signal X1 X2) {M r : ℕ} (hle : M ≤ r) :
    ancestorAt M (view1 (pre h r)) = view1 (pre h M) ∧
      ancestorAt M (view2 (pre h r)) = view2 (pre h M) := by
  unfold ancestorAt
  have vr := vround_views (pre h r)
  rw [pre_length_gen] at vr
  rw [vr.1, vr.2]
  have heq : pre h r = pre h (M + (r - M)) := congrArg (pre h) (by omega)
  rw [heq]
  exact viterPrev_pre h M (r - M)

lemma vcoord_views {X1 X2 : Type} (l : List (Signal X1 X2)) :
    let j := jIdx (l.map (fun s => s.2.2))
    if j % 2 = 0 then vcoord (view1 l) = j ∧ vcoord (view2 l) = j + 1
    else vcoord (view1 l) = j + 1 ∧ vcoord (view2 l) = j := by
  induction l using List.reverseRecOn with
  | nil => simp [jIdx, view1, view2, views, vcoord]
  | append_singleton l s ih =>
    rcases s with ⟨x1, x2, g⟩
    simp only [List.map_append, List.map_singleton, jIdx_append]
    set j := jIdx (l.map (fun s => s.2.2))
    have h1 : view1 (l ++ [(x1, x2, g)]) = (viewStep (view1 l, view2 l) (x1, x2, g)).1 := by
      simp [view1, view2, views]
    have h2 : view2 (l ++ [(x1, x2, g)]) = (viewStep (view1 l, view2 l) (x1, x2, g)).2 := by
      simp [view1, view2, views]
    rw [h1, h2]
    by_cases hj : j % 2 = 0
    · simp only [hj, ↓reduceIte] at ih
      cases g <;> simp only [stepJ, hj, ↓reduceIte, delta, viewStep, vcoord, ih.1, ih.2] <;>
        split_ifs <;> omega
    · simp only [hj, ↓reduceIte] at ih
      cases g <;> simp only [stepJ, hj, ↓reduceIte, delta, viewStep, vcoord, ih.1, ih.2] <;>
        split_ifs <;> omega

lemma vcoord_bounds {X1 X2 : Type} (l : List (Signal X1 X2)) :
    let j := jIdx (l.map (fun s => s.2.2))
    (j ≤ vcoord (view1 l) ∧ vcoord (view1 l) ≤ j + 1) ∧
    (j ≤ vcoord (view2 l) ∧ vcoord (view2 l) ≤ j + 1) := by
  have h := vcoord_views l
  dsimp only at h ⊢
  split_ifs at h <;> omega

def optProp1 {V : Type} : View V V → Option V
  | .I1 => none
  | .I2 => none
  | .N1 x1 u => if vround u = 0 then some x1 else optProp1 u
  | .N2 _ v => optProp1 v
  | .C1 x1 u _ _ => if vround u = 0 then some x1 else optProp1 u
  | .C2 _ _ x1 u => if vround u = 0 then some x1 else optProp1 u

def optProp2 {V : Type} : View V V → Option V
  | .I1 => none
  | .I2 => none
  | .N1 _ u => optProp2 u
  | .N2 x2 v => if vround v = 0 then some x2 else optProp2 v
  | .C1 _ _ x2 v => if vround v = 0 then some x2 else optProp2 v
  | .C2 x2 v _ _ => if vround v = 0 then some x2 else optProp2 v

def readProp1 {V : Type} (fallback : V) (v : View V V) : V :=
  (optProp1 v).getD fallback

def readProp2 {V : Type} (fallback : V) (v : View V V) : V :=
  (optProp2 v).getD fallback

lemma optProp1_view1 {V : Type} (l : List (Signal V V)) (hl : 0 < l.length) :
    optProp1 (view1 l) = some l[0].1 := by
  induction l using List.reverseRecOn with
  | nil => simp at hl
  | append_singleton l s ih =>
    rcases s with ⟨x1, x2, g⟩
    have h1 : view1 (l ++ [(x1, x2, g)]) = (viewStep (view1 l, view2 l) (x1, x2, g)).1 := by
      simp [view1, view2, views]
    rw [h1]
    have hr := (vround_views l).1
    by_cases hl0 : l.length = 0
    · have hnil : l = [] := List.eq_nil_of_length_eq_zero hl0
      subst hnil; cases g <;> rfl
    · have hpos : 0 < l.length := Nat.pos_of_ne_zero hl0
      rw [List.getElem_append_left hpos]
      cases g <;> simp [viewStep, optProp1, hr, hl0, ih hpos]

lemma optProp1_view2 {V : Type} (l : List (Signal V V)) :
    (optProp1 (view2 l) = none ∧ vcoord (view2 l) = 3 ^ l.length) ∨
      (∃ hl : 0 < l.length, optProp1 (view2 l) = some l[0].1) := by
  induction l using List.reverseRecOn with
  | nil => left; simp [view2, views, optProp1, vcoord]
  | append_singleton l s ih =>
    rcases s with ⟨x1, x2, g⟩
    have h2 : view2 (l ++ [(x1, x2, g)]) = (viewStep (view1 l, view2 l) (x1, x2, g)).2 := by
      simp [view1, view2, views]
    rw [h2]
    have hr := (vround_views l).1
    cases g with
    | oneToTwo =>
      right; refine ⟨by simp, ?_⟩
      by_cases hl0 : l.length = 0
      · have hnil : l = [] := List.eq_nil_of_length_eq_zero hl0
        subst hnil; rfl
      · have hpos : 0 < l.length := Nat.pos_of_ne_zero hl0
        rw [List.getElem_append_left hpos]
        simp [viewStep, optProp1, hr, hl0, optProp1_view1 l hpos]
    | both =>
      right; refine ⟨by simp, ?_⟩
      by_cases hl0 : l.length = 0
      · have hnil : l = [] := List.eq_nil_of_length_eq_zero hl0
        subst hnil; rfl
      · have hpos : 0 < l.length := Nat.pos_of_ne_zero hl0
        rw [List.getElem_append_left hpos]
        simp [viewStep, optProp1, hr, hl0, optProp1_view1 l hpos]
    | twoToOne =>
      rcases ih with ⟨hn, hc⟩ | ⟨hpos, hs⟩
      · left; refine ⟨by simp [viewStep, optProp1, hn], ?_⟩
        simp [viewStep, vcoord, hc, pow_succ]; ring
      · right; refine ⟨by simp, ?_⟩
        rw [List.getElem_append_left hpos]
        simp [viewStep, optProp1, hs]

lemma optProp2_view2 {V : Type} (l : List (Signal V V)) (hl : 0 < l.length) :
    optProp2 (view2 l) = some l[0].2.1 := by
  induction l using List.reverseRecOn with
  | nil => simp at hl
  | append_singleton l s ih =>
    rcases s with ⟨x1, x2, g⟩
    have h2 : view2 (l ++ [(x1, x2, g)]) = (viewStep (view1 l, view2 l) (x1, x2, g)).2 := by
      simp [view1, view2, views]
    rw [h2]
    have hr := (vround_views l).2
    by_cases hl0 : l.length = 0
    · have hnil : l = [] := List.eq_nil_of_length_eq_zero hl0
      subst hnil; cases g <;> rfl
    · have hpos : 0 < l.length := Nat.pos_of_ne_zero hl0
      rw [List.getElem_append_left hpos]
      cases g <;> simp [viewStep, optProp2, hr, hl0, ih hpos]

lemma optProp2_view1 {V : Type} (l : List (Signal V V)) :
    (optProp2 (view1 l) = none ∧ vcoord (view1 l) = 0) ∨
      (∃ hl : 0 < l.length, optProp2 (view1 l) = some l[0].2.1) := by
  induction l using List.reverseRecOn with
  | nil => left; simp [view1, views, optProp2, vcoord]
  | append_singleton l s ih =>
    rcases s with ⟨x1, x2, g⟩
    have h1 : view1 (l ++ [(x1, x2, g)]) = (viewStep (view1 l, view2 l) (x1, x2, g)).1 := by
      simp [view1, view2, views]
    rw [h1]
    have hr := (vround_views l).2
    cases g with
    | oneToTwo =>
      rcases ih with ⟨hn, hc⟩ | ⟨hpos, hs⟩
      · left; exact ⟨by simp [viewStep, optProp2, hn], by simp [viewStep, vcoord, hc]⟩
      · right; refine ⟨by simp, ?_⟩
        rw [List.getElem_append_left hpos]
        simp [viewStep, optProp2, hs]
    | both =>
      right; refine ⟨by simp, ?_⟩
      by_cases hl0 : l.length = 0
      · have hnil : l = [] := List.eq_nil_of_length_eq_zero hl0
        subst hnil; rfl
      · have hpos : 0 < l.length := Nat.pos_of_ne_zero hl0
        rw [List.getElem_append_left hpos]
        simp [viewStep, optProp2, hr, hl0, optProp2_view2 l hpos]
    | twoToOne =>
      right; refine ⟨by simp, ?_⟩
      by_cases hl0 : l.length = 0
      · have hnil : l = [] := List.eq_nil_of_length_eq_zero hl0
        subst hnil; rfl
      · have hpos : 0 < l.length := Nat.pos_of_ne_zero hl0
        rw [List.getElem_append_left hpos]
        simp [viewStep, optProp2, hr, hl0, optProp2_view2 l hpos]

lemma readProp1_known {V : Type} (fallback : V) (l : List (Signal V V)) (hl : 0 < l.length) :
    readProp1 fallback (view1 l) = l[0].1 ∧
      (vcoord (view2 l) < 3 ^ l.length → readProp1 fallback (view2 l) = l[0].1) := by
  constructor
  · simp [readProp1, optProp1_view1 l hl]
  · intro hc
    rcases optProp1_view2 l with ⟨_, heq⟩ | ⟨_, hs⟩
    · omega
    · simp [readProp1, hs]

lemma readProp2_known {V : Type} (fallback : V) (l : List (Signal V V)) (hl : 0 < l.length) :
    readProp2 fallback (view2 l) = l[0].2.1 ∧
      (0 < vcoord (view1 l) → readProp2 fallback (view1 l) = l[0].2.1) := by
  constructor
  · simp [readProp2, optProp2_view2 l hl]
  · intro hc
    rcases optProp2_view1 l with ⟨_, heq⟩ | ⟨_, hs⟩
    · omega
    · simp [readProp2, hs]

def gapRule {V : Type} (fallback : V) (cut : ℕ) (v : View V V) : V :=
  if vcoord v ≤ cut then readProp1 fallback v else readProp2 fallback v

lemma solvesWithin_of_missing_prefix {V : Type} [Nonempty V]
    (A : Set (ℕ → CommGraph)) (hole : List CommGraph)
    (hpos : 1 ≤ hole.length) (hmiss : hole ∉ Pref A) :
    ConsensusSolvableWithin V A hole.length := by
  classical
  let fallback : V := Classical.choice inferInstance
  set R := hole.length
  set cut := jIdx hole
  have hcut_lt : cut < 3 ^ R := jIdx_lt hole
  let fn : View V V → Option V := fun v =>
    if vround v < R then none else some (gapRule fallback cut (ancestorAt R v))
  let f : Algorithm V V (Option V) (Option V) := ⟨fn, fn⟩
  have hAt : ∀ (h : ℕ → Signal V V) (r : ℕ), R ≤ r →
      outAt1 f h r = some (gapRule fallback cut (view1 (pre h R))) ∧
      outAt2 f h r = some (gapRule fallback cut (view2 (pre h R))) := by
    intro h r hle
    have vr := vround_views (pre h r)
    rw [pre_length_gen] at vr
    have hanc := ancestorAt_pre h hle
    have hnotlt : ¬ (r < R) := by omega
    exact ⟨by simp [outAt1, f, fn, vr.1, hnotlt, hanc.1],
           by simp [outAt2, f, fn, vr.2, hnotlt, hanc.2]⟩
  refine ⟨f, ⟨?_, ?_⟩, ?_⟩
  · intro h _ r _
    by_cases hlt : r < R
    · have vr := vround_views (pre h r)
      rw [pre_length_gen] at vr
      have h1 : outAt1 f h r = none := by simp [outAt1, f, fn, vr.1, hlt]
      have h2 : outAt2 f h r = none := by simp [outAt2, f, fn, vr.2, hlt]
      exact ⟨fun o ho => by simp [h1] at ho,
             fun o ho => by simp [h2] at ho⟩
    · have ha := hAt h r (by omega)
      have hb := hAt h (r + 1) (by omega)
      exact ⟨fun o ho => by rw [ha.1] at ho; rw [hb.1, ho],
             fun o ho => by rw [ha.2] at ho; rw [hb.2, ho]⟩
  · intro h hg
    have ha := hAt h R le_rfl
    have hlive : pre (graphOf h) R ∈ Pref A := ⟨graphOf h, hg, by simp [pre_length_gen]⟩
    have hne_list : pre (graphOf h) R ≠ hole := fun heq => hmiss (heq ▸ hlive)
    have hne_idx : jIdx (pre (graphOf h) R) ≠ cut := fun heq =>
      hne_list (inj_list _ _ (pre_length_gen _ R) heq)
    set l := pre h R
    have hl : l.length = R := pre_length_gen h R
    have hlpos : 0 < l.length := by omega
    have h0_eq : l[0]'hlpos = h 0 := by simp [l, pre]
    have vb := vcoord_bounds l
    have hmap : l.map (fun s => s.2.2) = pre (graphOf h) R := by
      simp [l, pre, graphOf, Function.comp_def]
    rw [hmap] at vb
    have hk1 := readProp1_known fallback l hlpos
    have hk2 := readProp2_known fallback l hlpos
    set j := jIdx (pre (graphOf h) R)
    by_cases hj : j < cut
    · have hc1 : vcoord (view1 l) ≤ cut := by omega
      have hc2 : vcoord (view2 l) ≤ cut := by omega
      have hvc2_lt : vcoord (view2 l) < 3 ^ l.length := by rw [hl]; omega
      have hg1 : gapRule fallback cut (view1 l) = (h 0).1 := by
        simp [gapRule, hc1, hk1.1, h0_eq]
      have hg2 : gapRule fallback cut (view2 l) = (h 0).1 := by
        simp [gapRule, hc2, hk1.2 hvc2_lt, h0_eq]
      exact ⟨R, hpos, (h 0).1, (h 0).1, by rw [ha.1, hg1], by rw [ha.2, hg2], rfl, Or.inl rfl⟩
    · have hc1 : ¬ (vcoord (view1 l) ≤ cut) := by omega
      have hc2 : ¬ (vcoord (view2 l) ≤ cut) := by omega
      have hvc1_pos : 0 < vcoord (view1 l) := by omega
      have hg1 : gapRule fallback cut (view1 l) = (h 0).2.1 := by
        simp [gapRule, hc1, hk2.2 hvc1_pos, h0_eq]
      have hg2 : gapRule fallback cut (view2 l) = (h 0).2.1 := by
        simp [gapRule, hc2, hk2.1, h0_eq]
      exact ⟨R, hpos, (h 0).2.1, (h 0).2.1, by rw [ha.1, hg1], by rw [ha.2, hg2], rfl, Or.inr rfl⟩
  · intro h _ r _
    constructor
    · intro hnone
      by_contra hnlt
      have ha := (hAt h r (by omega)).1
      rw [ha] at hnone
      cases hnone
    · intro hnone
      by_contra hnlt
      have ha := (hAt h r (by omega)).2
      rw [ha] at hnone
      cases hnone

/-! ### DPA live states, shift invariance, and pigeonhole loop removal -/

def runFrom {S α : Type} (M : DPA S α) (q : S) (w : ℕ → α) : ℕ → S
  | 0 => q
  | n + 1 => M.step (runFrom M q w n) (w n)

def AcceptsFrom {S α : Type} (M : DPA S α) (q : S) (w : ℕ → α) : Prop :=
  ParityCond (fun n => M.prio (runFrom M q w n))

def LiveState {S α : Type} (M : DPA S α) (q : S) : Prop :=
  ∃ w : ℕ → α, AcceptsFrom M q w

lemma run_eq_runFrom {S α : Type} (M : DPA S α) (w : ℕ → α) :
    ∀ n, M.run w n = runFrom M M.init w n
  | 0 => rfl
  | n + 1 => by simp [DPA.run, runFrom, run_eq_runFrom M w n]

lemma runFrom_succ_word {S α : Type} (M : DPA S α) (q : S) (v : ℕ → α) :
    ∀ m, runFrom M q v (m + 1) = runFrom M (M.step q (v 0)) (fun k => v (k + 1)) m
  | 0 => rfl
  | m + 1 => by
      change M.step (runFrom M q v (m + 1)) (v (m + 1)) =
        M.step (runFrom M (M.step q (v 0)) (fun k => v (k + 1)) m) (v (m + 1))
      rw [runFrom_succ_word M q v m]

lemma append_nil_eq {α : Type} (w : ℕ → α) : append ([] : List α) w = w := by
  funext n; simp [append]

lemma append_cons_succ {α : Type} (a : α) (u : List α) (w : ℕ → α) :
    (fun k => append (a :: u) w (k + 1)) = append u w := by
  funext k
  simp [append]

lemma runFrom_append {S α : Type} (M : DPA S α) (u : List α) (q : S) (w : ℕ → α) (n : ℕ) :
    runFrom M q (append u w) (u.length + n) = runFrom M (u.foldl M.step q) w n := by
  induction u generalizing q with
  | nil => simp [append_nil_eq]
  | cons a u ih =>
    have hlen : (a :: u).length + n = (u.length + n) + 1 := by simp; omega
    rw [hlen, runFrom_succ_word, append_cons_succ]
    have h0 : append (a :: u) w 0 = a := by simp [append]
    rw [h0]
    exact ih (M.step q a)

lemma parityCond_shift (P : ℕ → ℕ) (d : ℕ) :
    ParityCond P ↔ ParityCond (fun n => P (d + n)) := by
  unfold ParityCond
  constructor
  · rintro ⟨p, heven, hfreq, hev⟩
    refine ⟨p, heven, ?_, ?_⟩
    · rw [Filter.frequently_atTop] at hfreq ⊢
      intro N
      obtain ⟨n, hn, hp⟩ := hfreq (d + N)
      refine ⟨n - d, by omega, ?_⟩
      dsimp only
      rwa [show d + (n - d) = n by omega]
    · rw [Filter.eventually_atTop] at hev ⊢
      obtain ⟨N, hN⟩ := hev
      exact ⟨N, fun n hn => hN (d + n) (by omega)⟩
  · rintro ⟨p, heven, hfreq, hev⟩
    refine ⟨p, heven, ?_, ?_⟩
    · rw [Filter.frequently_atTop] at hfreq ⊢
      intro N
      obtain ⟨n, hn, hp⟩ := hfreq N
      exact ⟨d + n, by omega, hp⟩
    · rw [Filter.eventually_atTop] at hev ⊢
      obtain ⟨N, hN⟩ := hev
      refine ⟨d + N, fun n hn => ?_⟩
      have hle := hN (n - d) (by omega)
      dsimp only at hle
      rwa [show d + (n - d) = n by omega] at hle

lemma acceptsFrom_append_iff {S α : Type} (M : DPA S α) (q : S) (u : List α) (w : ℕ → α) :
    AcceptsFrom M q (append u w) ↔ AcceptsFrom M (u.foldl M.step q) w := by
  unfold AcceptsFrom
  rw [parityCond_shift _ u.length]
  have heq : (fun n => M.prio (runFrom M q (append u w) (u.length + n))) =
      (fun n => M.prio (runFrom M (u.foldl M.step q) w n)) := by
    funext n
    rw [runFrom_append]
  rw [heq]

lemma pre_append_eq {α : Type} (u : List α) (w : ℕ → α) :
    pre (append u w) u.length = u := by
  apply List.ext_getElem
  · simp [pre]
  · intro i h1 h2; simp [pre, append]

lemma eq_append_of_pre {α : Type} (w : ℕ → α) (u : List α) (h : pre w u.length = u) :
    w = append u (fun n => w (u.length + n)) := by
  funext n
  unfold append
  split_ifs with hn
  · have hget := congrArg (fun l => l[n]?) h
    simpa [pre, hn] using hget
  · congr 1
    omega

lemma mem_pref_lang_iff {S α : Type} (M : DPA S α) (u : List α) :
    u ∈ Pref M.lang ↔ LiveState M (u.foldl M.step M.init) := by
  constructor
  · rintro ⟨w, hw, hpre⟩
    have hw_eq := eq_append_of_pre w u hpre
    have hacc : AcceptsFrom M M.init w := by
      change ParityCond _
      have heq : (fun n => M.prio (runFrom M M.init w n)) = (fun n => M.prio (M.run w n)) := by
        funext n; rw [run_eq_runFrom]
      rw [heq]; exact hw
    rw [hw_eq, acceptsFrom_append_iff] at hacc
    exact ⟨fun n => w (u.length + n), hacc⟩
  · rintro ⟨w, hacc⟩
    have hacc0 : AcceptsFrom M M.init (append u w) :=
      (acceptsFrom_append_iff M M.init u w).mpr hacc
    have hmem : append u w ∈ M.lang := by
      change ParityCond _
      have heq : (fun n => M.prio (M.run (append u w) n)) =
          (fun n => M.prio (runFrom M M.init (append u w) n)) := by
        funext n; rw [run_eq_runFrom]
      rw [heq]; exact hacc0
    exact ⟨append u w, hmem, pre_append_eq u w⟩

lemma dead_foldl_closed {S α : Type} (M : DPA S α) (q : S) (pad : List α)
    (hdead : ¬ LiveState M q) : ¬ LiveState M (pad.foldl M.step q) := by
  rintro ⟨w, hw⟩
  exact hdead ⟨append pad w, (acceptsFrom_append_iff M q pad w).mpr hw⟩

lemma shorten_walk {S α : Type} [Fintype S] (M : DPA S α) (q0 : S) (k : List α) :
    ∃ k0 : List α, k0.length < Fintype.card S ∧ k0.foldl M.step q0 = k.foldl M.step q0 := by
  suffices ∀ (n : ℕ) (l : List α), l.length = n →
      ∃ k0 : List α, k0.length < Fintype.card S ∧ k0.foldl M.step q0 = l.foldl M.step q0 from
    this k.length k rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro l hlen
    by_cases hlt : n < Fintype.card S
    · exact ⟨l, hlen ▸ hlt, rfl⟩
    · let f : Fin (Fintype.card S + 1) → S := fun i => (l.take i.val).foldl M.step q0
      obtain ⟨a, b, hab, heq⟩ :=
        Fintype.exists_ne_map_eq_of_card_lt f (by simp)
      have hne_val : a.val ≠ b.val := fun hv => hab (Fin.ext hv)
      obtain ⟨i, j, hij, hij_le, hfi⟩ :
          ∃ i j : ℕ, i < j ∧ j ≤ l.length ∧
            (l.take i).foldl M.step q0 = (l.take j).foldl M.step q0 := by
        rcases lt_or_gt_of_ne hne_val with hlt_ab | hgt_ab
        · exact ⟨a.val, b.val, hlt_ab, by omega, heq⟩
        · exact ⟨b.val, a.val, hgt_ab, by omega, heq.symm⟩
      let l' := l.take i ++ l.drop j
      have hlen' : l'.length < n := by
        simp only [l', List.length_append, List.length_take, List.length_drop, hlen]
        omega
      have hfold' : l'.foldl M.step q0 = l.foldl M.step q0 := by
        conv_rhs => rw [← List.take_append_drop j l]
        simp only [l', List.foldl_append, hfi]
      obtain ⟨k0, hk0_len, hk0_fold⟩ := ih l'.length hlen' l' rfl
      exact ⟨k0, hk0_len, hk0_fold.trans hfold'⟩

lemma append_append_eq {α : Type} (h k : List α) (w : ℕ → α) :
    append h (append k w) = append (h ++ k) w := by
  funext n
  simp only [append, List.length_append]
  by_cases hn : n < h.length
  · have hn2 : n < h.length + k.length := by omega
    simp [hn, hn2, List.getElem_append_left hn]
  · by_cases hk : n - h.length < k.length
    · have hn2 : n < h.length + k.length := by omega
      simp [hn, hk, hn2, List.getElem_append_right (Nat.le_of_not_lt hn)]
    · have hn2 : ¬ (n < h.length + k.length) := by omega
      simp [hn, hk, hn2]
      congr 1
      omega

lemma not_mem_pref_leftQuot {α : Type} (A : Set (ℕ → α)) (h hole : List α)
    (hmiss : h ++ hole ∉ Pref A) : hole ∉ Pref (leftQuot h A) := by
  rintro ⟨w, hw, hpre⟩
  apply hmiss
  have hw_eq := eq_append_of_pre w hole hpre
  change append h w ∈ A at hw
  rw [hw_eq, append_append_eq] at hw
  exact ⟨append (h ++ hole) (fun n => w (hole.length + n)), hw, pre_append_eq (h ++ hole) _⟩

end DistLTLSynth.Char.Lemma36Aux

open DistLTLSynth.Char DistLTLSynth.Char.Lemma36Aux in
theorem solution (V : Type) [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V) :
    ∃ D : DPACode → ℕ, Computable D ∧
      ∀ c : DPACode, IsNowhereDense (piMap '' c.lang) →
        1 ≤ D c ∧
          ∀ h ∈ Pref c.lang, ConsensusSolvableWithin V (leftQuot h c.lang) (D c) := by
  refine ⟨fun c => c.1 + 1, ?_, ?_⟩
  · exact (Primrec.succ.comp Primrec.fst).to_comp
  · intro c hND
    refine ⟨Nat.succ_pos c.1, ?_⟩
    intro h _
    let M := c.toDPA
    obtain ⟨k, hk_miss⟩ := (lemma_6_15 c.lang).mp hND h
    have hdead_k : ¬ LiveState M ((h ++ k).foldl M.step M.init) :=
      fun hlive => hk_miss ((mem_pref_lang_iff M (h ++ k)).mpr hlive)
    rw [List.foldl_append] at hdead_k
    set q0 := h.foldl M.step M.init
    obtain ⟨k0, hk0_lt, hk0_fold⟩ := shorten_walk M q0 k
    simp only [Fintype.card_fin] at hk0_lt
    have hdead_k0 : ¬ LiveState M (k0.foldl M.step q0) := hk0_fold.symm ▸ hdead_k
    let pad := List.replicate (c.1 + 1 - k0.length) CommGraph.both
    let hole := k0 ++ pad
    have hhole_len : hole.length = c.1 + 1 := by
      simp only [hole, pad, List.length_append, List.length_replicate]
      omega
    have hdead_hole : ¬ LiveState M ((h ++ hole).foldl M.step M.init) := by
      rw [List.foldl_append]
      change ¬ LiveState M ((k0 ++ pad).foldl M.step q0)
      rw [List.foldl_append]
      exact dead_foldl_closed M _ pad hdead_k0
    have hmiss_hole : h ++ hole ∉ Pref c.lang :=
      fun hlive => hdead_hole ((mem_pref_lang_iff M (h ++ hole)).mp hlive)
    have hmiss_quot : hole ∉ Pref (leftQuot h c.lang) :=
      not_mem_pref_leftQuot c.lang h hole hmiss_hole
    have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    dsimp only
    rw [← hhole_len]
    exact solvesWithin_of_missing_prefix (leftQuot h c.lang) hole (by omega) hmiss_quot
