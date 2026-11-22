-- Prove2me | solution 1 for DistLTLSynth.Char.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T07:15:10.909578+00:00
-- url     : https://prove2.me/submissions/91012bda-432a-42a4-9a03-2ecf5a7250a2

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_Geometric
import Definitions.Def_DistLTLSynth_Char_Consensus
import Theorems.Thm_DistLTLSynth_Char_lemma_2_4
import Theorems.Thm_DistLTLSynth_Char_lemma_3_1

namespace DistLTLSynth.Char.Lemma52Aux
open DistLTLSynth.Char

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

/-! ### Local view round, spine ancestor, coordinate, and known proposals -/

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
      subst hnil
      cases g <;> rfl
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

/-! ### Gap-table bounded consensus from a missing finite prefix -/

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
  · -- Irrevocability
    intro h _ r _
    by_cases hlt : r < R
    · have vr := vround_views (pre h r)
      rw [pre_length_gen] at vr
      have h1 : outAt1 f h r = none := by simp [outAt1, f, fn, vr.1, hlt]
      have h2 : outAt2 f h r = none := by simp [outAt2, f, fn, vr.2, hlt]
      exact ⟨fun o ho => by simp [h1] at ho,
             fun o ho => by simp [h2] at ho⟩
    · have hle : R ≤ r := by omega
      have hle' : R ≤ r + 1 := by omega
      have ha := hAt h r hle
      have hb := hAt h (r + 1) hle'
      exact ⟨fun o ho => by rw [ha.1] at ho; rw [hb.1, ho],
             fun o ho => by rw [ha.2] at ho; rw [hb.2, ho]⟩
  · -- Agreement and validity at round R
    intro h hg
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
    · have hj_gt : cut < j := by omega
      have hc1 : ¬ (vcoord (view1 l) ≤ cut) := by omega
      have hc2 : ¬ (vcoord (view2 l) ≤ cut) := by omega
      have hvc1_pos : 0 < vcoord (view1 l) := by omega
      have hg1 : gapRule fallback cut (view1 l) = (h 0).2.1 := by
        simp [gapRule, hc1, hk2.2 hvc1_pos, h0_eq]
      have hg2 : gapRule fallback cut (view2 l) = (h 0).2.1 := by
        simp [gapRule, hc2, hk2.1, h0_eq]
      exact ⟨R, hpos, (h 0).2.1, (h 0).2.1, by rw [ha.1, hg1], by rw [ha.2, hg2], rfl, Or.inr rfl⟩
  · -- DecidesWithin R
    intro h _ r _
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

/-! ### Topological lemmas connecting `closure A` and `closure (piMap '' A)` -/

lemma closure_image_piMap (A : Set (ℕ → CommGraph)) :
    closure (piMap '' A) = piMap '' closure A := by
  have hcont := lemma_2_4.1
  apply Set.Subset.antisymm
  · exact closure_minimal (Set.image_mono subset_closure)
      ((isClosed_closure.isCompact.image hcont).isClosed)
  · exact image_closure_subset_closure_image hcont

lemma cylinder_isOpen (g : ℕ → CommGraph) (M : ℕ) :
    IsOpen {w : ℕ → CommGraph | ∀ k < M, w k = g k} := by
  have h : IsOpen (⋂ k ∈ Finset.range M, {w : ℕ → CommGraph | w k = g k}) :=
    isOpen_biInter_finset fun k _ => by
      have hc : Continuous (fun w : ℕ → CommGraph => w k) := continuous_apply k
      exact hc.isOpen_preimage {g k} (isOpen_discrete _)
  convert h using 1
  ext w
  simp only [Set.mem_iInter, Finset.mem_range]
  rfl

lemma solves_persist {V : Type} {f : Algorithm V V (Option V) (Option V)}
    {A : Set (ℕ → CommGraph)} (hf : Solves (consensus V) f A)
    {h : ℕ → Signal V V} (hg : graphOf h ∈ A) :
    ∀ {r r' : ℕ}, 1 ≤ r → r ≤ r' → ∀ o : V,
      (outAt1 f h r = some o → outAt1 f h r' = some o) ∧
      (outAt2 f h r = some o → outAt2 f h r' = some o) := by
  intro r r' hr hle o
  obtain ⟨d, rfl⟩ : ∃ d, r' = r + d := ⟨r' - r, by omega⟩
  clear hle
  induction d with
  | zero => simp
  | succ d ih =>
    have hstep := hf.1 h hg (r + d) (by omega)
    exact ⟨fun h1 => hstep.1 o (ih.1 h1), fun h2 => hstep.2 o (ih.2 h2)⟩

end DistLTLSynth.Char.Lemma52Aux

open DistLTLSynth.Char DistLTLSynth.Char.Lemma52Aux in
theorem solution (V : Type) [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V)
    (A : Set (ℕ → CommGraph)) :
    ConsensusSolvableBounded V A ↔ closure (piMap '' A) ≠ Set.Icc (0 : ℝ) 1 := by
  classical
  constructor
  · rintro ⟨R, f, hf, hdec⟩
    set M := max R 1
    have hM1 : 1 ≤ M := le_max_right R 1
    have hRM : R ≤ M := le_max_left R 1
    -- For every execution in `A`, `f` already outputs valid agreed decisions at round `M`
    have hAtM : ∀ h : ℕ → Signal V V, graphOf h ∈ A →
        ∃ v : V, f.f1 (view1 (pre h M)) = some v ∧
          f.f2 (view2 (pre h M)) = some v ∧ (v = (h 0).1 ∨ v = (h 0).2.1) := by
      intro h hg
      obtain ⟨r0, hr0, o1, o2, ho1, ho2, heq, hval⟩ := hf.2 h hg
      dsimp only at heq hval
      subst heq
      have hn1 : outAt1 f h M ≠ none := fun hn => by
        have := (hdec h hg M hM1).1 hn; omega
      have hn2 : outAt2 f h M ≠ none := fun hn => by
        have := (hdec h hg M hM1).2 hn; omega
      obtain ⟨u1, hu1⟩ := Option.ne_none_iff_exists'.mp hn1
      obtain ⟨u2, hu2⟩ := Option.ne_none_iff_exists'.mp hn2
      have hp1 := (solves_persist hf hg hM1 (le_max_left M r0) u1).1 hu1
      have hp1' := (solves_persist hf hg hr0 (le_max_right M r0) o1).1 ho1
      have hp2 := (solves_persist hf hg hM1 (le_max_left M r0) u2).2 hu2
      have hp2' := (solves_persist hf hg hr0 (le_max_right M r0) o1).2 ho2
      have e1 : u1 = o1 := Option.some.inj (hp1.symm.trans hp1')
      have e2 : u2 = o1 := Option.some.inj (hp2.symm.trans hp2')
      exact ⟨o1, e1 ▸ hu1, e2 ▸ hu2, hval⟩
    -- Modify `f` to `f'` that waits until round `M` and freezes round-`M` outputs
    let f' : Algorithm V V (Option V) (Option V) :=
      ⟨fun v => if vround v < M then none else f.f1 (ancestorAt M v),
       fun v => if vround v < M then none else f.f2 (ancestorAt M v)⟩
    have hf'_eval : ∀ (h : ℕ → Signal V V) (r : ℕ), M ≤ r →
        outAt1 f' h r = f.f1 (view1 (pre h M)) ∧
        outAt2 f' h r = f.f2 (view2 (pre h M)) := by
      intro h r hle
      have vr := vround_views (pre h r)
      rw [pre_length_gen] at vr
      have hanc := ancestorAt_pre h hle
      have hnotlt : ¬ (r < M) := by omega
      exact ⟨by simp [outAt1, f', vr.1, hnotlt, hanc.1],
             by simp [outAt2, f', vr.2, hnotlt, hanc.2]⟩
    have hsol_cl : ConsensusSolvable V (closure A) := by
      refine ⟨f', ?_, ?_⟩
      · intro h _ r _
        by_cases hlt : r < M
        · have vr := vround_views (pre h r)
          rw [pre_length_gen] at vr
          have h1 : outAt1 f' h r = none := by simp [outAt1, f', vr.1, hlt]
          have h2 : outAt2 f' h r = none := by simp [outAt2, f', vr.2, hlt]
          exact ⟨fun o ho => by simp [h1] at ho,
                 fun o ho => by simp [h2] at ho⟩
        · have ha := hf'_eval h r (by omega)
          have hb := hf'_eval h (r + 1) (by omega)
          exact ⟨fun o ho => by rw [ha.1] at ho; rw [hb.1, ho],
                 fun o ho => by rw [ha.2] at ho; rw [hb.2, ho]⟩
      · intro h hg_cl
        obtain ⟨w, hw_cyl, hwA⟩ :=
          mem_closure_iff.mp hg_cl _ (cylinder_isOpen (graphOf h) M) (fun _ _ => rfl)
        let h' : ℕ → Signal V V := fun n => ((h n).1, (h n).2.1, w n)
        have hpre_eq : pre h' M = pre h M := by
          unfold pre
          congr 1
          funext i
          cases hni : h i.val with
          | mk x1 rest =>
            cases rest with
            | mk x2 gi =>
              have hwi : w i.val = gi := by
                have := hw_cyl i.val i.isLt
                simpa [graphOf, hni] using this
              simp [h', hni, hwi]
        obtain ⟨v, hv1, hv2, hval⟩ := hAtM h' hwA
        rw [hpre_eq] at hv1 hv2
        have ha := hf'_eval h M le_rfl
        exact ⟨M, hM1, v, v, by rw [ha.1, hv1], by rw [ha.2, hv2], rfl, hval⟩
    rw [closure_image_piMap]
    exact (lemma_3_1 V hV (closure A)).mp hsol_cl
  · intro hnot
    have hex_hole : ∃ hole : List CommGraph, hole ∉ Pref A := by
      by_contra hall
      have hall' : ∀ u : List CommGraph, u ∈ Pref A :=
        fun u => Classical.not_not.mp fun hm => hall ⟨u, hm⟩
      have hdense : Dense A := by
        rw [dense_iff_inter_open]
        rintro U hU ⟨v0, hv0⟩
        obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hU v0 hv0
        set r := I.sup id + 1
        obtain ⟨w, hwA, hw⟩ := hall' (pre v0 r)
        rw [pre_length_gen] at hw
        refine ⟨w, ?_, hwA⟩
        apply hsub
        intro a ha
        have har : a < r := Nat.lt_succ_of_le (Finset.le_sup (f := id) ha)
        have hget := congrArg (fun l => l[a]?) hw
        simp only [pre, List.getElem?_ofFn, har, ↓reduceDIte, Option.some.injEq] at hget
        show w a ∈ u a
        rw [hget]
        exact (hu a ha).2
      apply hnot
      rw [closure_image_piMap, hdense.closure_eq, Set.image_univ, lemma_2_4.2]
    obtain ⟨hole, hmiss⟩ := hex_hole
    let hole' := hole ++ [CommGraph.both]
    have hmiss' : hole' ∉ Pref A := by
      rintro ⟨w, hwA, hw⟩
      apply hmiss
      refine ⟨w, hwA, ?_⟩
      apply List.ext_getElem
      · simp [pre]
      · intro i hi1 hi2
        have hlen : hole'.length = hole.length + 1 := by simp [hole']
        have hi' : i < hole'.length := by omega
        have hget := congrArg (fun l => l[i]?) hw
        simp only [pre, List.getElem?_ofFn, hi', ↓reduceDIte] at hget
        rw [List.getElem?_eq_getElem hi'] at hget
        injection hget with hget
        simp only [pre, List.getElem_ofFn, hget]
        exact List.getElem_append_left hi2
    have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    exact ⟨hole'.length, solvesWithin_of_missing_prefix A hole' (by simp [hole']) hmiss'⟩
