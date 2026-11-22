-- Prove2me | solution 1 for DistLTLSynth.Char.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T07:10:41.456266+00:00
-- url     : https://prove2.me/submissions/87fb55bf-6dc2-4c8e-98bc-0e22c7681d51

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_Geometric
import Definitions.Def_DistLTLSynth_Char_Consensus

namespace DistLTLSynth.Char.Lemma31Aux
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

noncomputable def lo (w : ℕ → CommGraph) (r : ℕ) : ℝ :=
  (jIdx (pre w r) : ℝ) / 3 ^ r

lemma lo_mono (w : ℕ → CommGraph) : Monotone (lo w) := by
  apply monotone_nat_of_le_succ
  intro r
  have hb := stepJ_bounds (jIdx (pre w r)) (w r)
  unfold lo
  rw [pre_succ_gen, jIdx_append]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (3 * (jIdx (pre w r)) : ℝ) ≤ (stepJ (jIdx (pre w r)) (w r) : ℝ) := by exact_mod_cast hb.1
  rw [pow_succ]
  nlinarith [pow_pos (show (0 : ℝ) < 3 by norm_num) r]

lemma hi_anti (w : ℕ → CommGraph) : Antitone (fun r => lo w r + 1 / 3 ^ r) := by
  apply antitone_nat_of_succ_le
  intro r
  have hb := stepJ_bounds (jIdx (pre w r)) (w r)
  unfold lo
  rw [pre_succ_gen, jIdx_append]
  have h3 : (stepJ (jIdx (pre w r)) (w r) : ℝ) ≤ 3 * (jIdx (pre w r)) + 2 := by exact_mod_cast hb.2
  have hp : (0 : ℝ) < 3 ^ r := by positivity
  have e1 : (stepJ (jIdx (pre w r)) (w r) : ℝ) / 3 ^ (r + 1) + 1 / 3 ^ (r + 1)
      = ((stepJ (jIdx (pre w r)) (w r) : ℝ) + 1) / (3 * 3 ^ r) := by rw [pow_succ]; ring
  have e2 : (jIdx (pre w r) : ℝ) / 3 ^ r + 1 / 3 ^ r = ((jIdx (pre w r) : ℝ) + 1) / 3 ^ r := by
    ring
  rw [e1, e2, div_le_div_iff₀ (by positivity) hp]
  nlinarith

lemma lo_le_hi (w : ℕ → CommGraph) (s r : ℕ) : lo w s ≤ lo w r + 1 / 3 ^ r := by
  rcases le_total s r with h | h
  · have := lo_mono w h
    have : (0 : ℝ) ≤ 1 / 3 ^ r := by positivity
    linarith
  · have := hi_anti w h
    have : (0 : ℝ) < 1 / 3 ^ s := by positivity
    linarith

lemma bdd_lo (w : ℕ → CommGraph) : BddAbove (Set.range (lo w)) :=
  ⟨lo w 0 + 1 / 3 ^ 0, by rintro _ ⟨s, rfl⟩; exact lo_le_hi w s 0⟩

lemma piMap_mem (w : ℕ → CommGraph) (r : ℕ) :
    lo w r ≤ piMap w ∧ piMap w ≤ lo w r + 1 / 3 ^ r :=
  ⟨le_ciSup (bdd_lo w) r, ciSup_le (fun s => lo_le_hi w s r)⟩

lemma lo_zero (w : ℕ → CommGraph) : lo w 0 = 0 := by
  simp [lo, pre, jIdx]

lemma range_sub (A : Set (ℕ → CommGraph)) : piMap '' A ⊆ Set.Icc (0 : ℝ) 1 := by
  rintro _ ⟨w, -, rfl⟩
  have h0 := piMap_mem w 0
  rw [lo_zero] at h0
  exact ⟨h0.1, by simpa using h0.2⟩

lemma piMap_mul_bounds (w : ℕ → CommGraph) (r : ℕ) :
    (jIdx (pre w r) : ℝ) ≤ piMap w * (3 : ℝ) ^ r ∧
      piMap w * (3 : ℝ) ^ r ≤ (jIdx (pre w r) : ℝ) + 1 := by
  have hm := piMap_mem w r
  have hp : (0 : ℝ) < (3 : ℝ) ^ r := by positivity
  unfold lo at hm
  constructor
  · exact (div_le_iff₀ hp).mp hm.1
  · have h2 : piMap w ≤ ((jIdx (pre w r) : ℝ) + 1) / (3 : ℝ) ^ r := by
      have heq : (jIdx (pre w r) : ℝ) / (3 : ℝ) ^ r + 1 / (3 : ℝ) ^ r =
          ((jIdx (pre w r) : ℝ) + 1) / (3 : ℝ) ^ r := by ring
      linarith [hm.2]
    exact (le_div_iff₀ hp).mp h2

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

lemma hpow (ε : ℝ) (hε : 0 < ε) : ∃ r : ℕ, 1 / (3 : ℝ) ^ r < ε := by
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε (show (1 : ℝ) / 3 < 1 by norm_num)
  exact ⟨r, by simpa [div_pow] using hr⟩

/-! ### Local view round, coordinate, known proposals, and latching -/

def vround {X1 X2 : Type} : View X1 X2 → ℕ
  | .I1 => 0
  | .I2 => 0
  | .N1 _ u => vround u + 1
  | .N2 _ v => vround v + 1
  | .C1 _ u _ _ => vround u + 1
  | .C2 _ v _ _ => vround v + 1

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
      have hget : (l ++ [(x1, x2, g)])[0] = l[0] := List.getElem_append_left hpos
      rw [hget]
      cases g <;> simp [viewStep, optProp1, hr, hl0, ih hpos]

lemma optProp1_view2 {V : Type} (l : List (Signal V V)) :
    (optProp1 (view2 l) = none ∧ vcoord (view2 l) = 3 ^ l.length) ∨
      (∃ hl : 0 < l.length, optProp1 (view2 l) = some l[0].1) := by
  induction l using List.reverseRecOn with
  | nil =>
    left
    simp [view2, views, optProp1, vcoord]
  | append_singleton l s ih =>
    rcases s with ⟨x1, x2, g⟩
    have h2 : view2 (l ++ [(x1, x2, g)]) = (viewStep (view1 l, view2 l) (x1, x2, g)).2 := by
      simp [view1, view2, views]
    rw [h2]
    have hr := (vround_views l).1
    cases g with
    | oneToTwo =>
      right
      refine ⟨by simp, ?_⟩
      by_cases hl0 : l.length = 0
      · have hnil : l = [] := List.eq_nil_of_length_eq_zero hl0
        subst hnil
        rfl
      · have hpos : 0 < l.length := Nat.pos_of_ne_zero hl0
        rw [List.getElem_append_left hpos]
        simp [viewStep, optProp1, hr, hl0, optProp1_view1 l hpos]
    | both =>
      right
      refine ⟨by simp, ?_⟩
      by_cases hl0 : l.length = 0
      · have hnil : l = [] := List.eq_nil_of_length_eq_zero hl0
        subst hnil
        rfl
      · have hpos : 0 < l.length := Nat.pos_of_ne_zero hl0
        rw [List.getElem_append_left hpos]
        simp [viewStep, optProp1, hr, hl0, optProp1_view1 l hpos]
    | twoToOne =>
      rcases ih with ⟨hn, hc⟩ | ⟨hpos, hs⟩
      · left
        refine ⟨by simp [viewStep, optProp1, hn], ?_⟩
        simp [viewStep, vcoord, hc, pow_succ]
        ring
      · right
        refine ⟨by simp, ?_⟩
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
      subst hnil
      cases g <;> rfl
    · have hpos : 0 < l.length := Nat.pos_of_ne_zero hl0
      have hget : (l ++ [(x1, x2, g)])[0] = l[0] := List.getElem_append_left hpos
      rw [hget]
      cases g <;> simp [viewStep, optProp2, hr, hl0, ih hpos]

lemma optProp2_view1 {V : Type} (l : List (Signal V V)) :
    (optProp2 (view1 l) = none ∧ vcoord (view1 l) = 0) ∨
      (∃ hl : 0 < l.length, optProp2 (view1 l) = some l[0].2.1) := by
  induction l using List.reverseRecOn with
  | nil =>
    left
    simp [view1, views, optProp2, vcoord]
  | append_singleton l s ih =>
    rcases s with ⟨x1, x2, g⟩
    have h1 : view1 (l ++ [(x1, x2, g)]) = (viewStep (view1 l, view2 l) (x1, x2, g)).1 := by
      simp [view1, view2, views]
    rw [h1]
    have hr := (vround_views l).2
    cases g with
    | oneToTwo =>
      rcases ih with ⟨hn, hc⟩ | ⟨hpos, hs⟩
      · left
        exact ⟨by simp [viewStep, optProp2, hn], by simp [viewStep, vcoord, hc]⟩
      · right
        refine ⟨by simp, ?_⟩
        rw [List.getElem_append_left hpos]
        simp [viewStep, optProp2, hs]
    | both =>
      right
      refine ⟨by simp, ?_⟩
      by_cases hl0 : l.length = 0
      · have hnil : l = [] := List.eq_nil_of_length_eq_zero hl0
        subst hnil
        rfl
      · have hpos : 0 < l.length := Nat.pos_of_ne_zero hl0
        rw [List.getElem_append_left hpos]
        simp [viewStep, optProp2, hr, hl0, optProp2_view2 l hpos]
    | twoToOne =>
      right
      refine ⟨by simp, ?_⟩
      by_cases hl0 : l.length = 0
      · have hnil : l = [] := List.eq_nil_of_length_eq_zero hl0
        subst hnil
        rfl
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

def latch {X1 X2 Y : Type} (cand : View X1 X2 → Option Y) : View X1 X2 → Option Y
  | .I1 => none
  | .I2 => none
  | .N1 x1 u => (latch cand u).or (cand (.N1 x1 u))
  | .N2 x2 v => (latch cand v).or (cand (.N2 x2 v))
  | .C1 x1 u x2 v => (latch cand u).or (cand (.C1 x1 u x2 v))
  | .C2 x2 v x1 u => (latch cand v).or (cand (.C2 x2 v x1 u))

lemma latch_view1_succ {X1 X2 Y : Type} (cand : View X1 X2 → Option Y)
    (h : ℕ → Signal X1 X2) (r : ℕ) :
    latch cand (view1 (pre h (r + 1))) =
      (latch cand (view1 (pre h r))).or (cand (view1 (pre h (r + 1)))) := by
  rw [pre_succ_gen]
  rcases hr : h r with ⟨x1, x2, g⟩
  have h1 : view1 (pre h r ++ [(x1, x2, g)]) =
      (viewStep (view1 (pre h r), view2 (pre h r)) (x1, x2, g)).1 := by
    simp [view1, view2, views]
  rw [h1]
  cases g <;> rfl

lemma latch_view2_succ {X1 X2 Y : Type} (cand : View X1 X2 → Option Y)
    (h : ℕ → Signal X1 X2) (r : ℕ) :
    latch cand (view2 (pre h (r + 1))) =
      (latch cand (view2 (pre h r))).or (cand (view2 (pre h (r + 1)))) := by
  rw [pre_succ_gen]
  rcases hr : h r with ⟨x1, x2, g⟩
  have h2 : view2 (pre h r ++ [(x1, x2, g)]) =
      (viewStep (view1 (pre h r), view2 (pre h r)) (x1, x2, g)).2 := by
    simp [view1, view2, views]
  rw [h2]
  cases g <;> rfl

lemma latch_view1_consistent {X1 X2 Y : Type} (cand : View X1 X2 → Option Y)
    (h : ℕ → Signal X1 X2) (target : Y)
    (hcons : ∀ r ≥ 1, ∀ o, cand (view1 (pre h r)) = some o → o = target) :
    ∀ r o, latch cand (view1 (pre h r)) = some o → o = target := by
  intro r
  induction r with
  | zero =>
    intro o ho
    simp [pre, view1, views, latch] at ho
  | succ r ih =>
    intro o ho
    rw [latch_view1_succ] at ho
    cases hl : latch cand (view1 (pre h r)) with
    | none =>
      rw [hl, Option.none_or] at ho
      exact hcons (r + 1) (by omega) o ho
    | some o' =>
      rw [hl, Option.some_or] at ho
      injection ho with heq
      rw [← heq]
      exact ih o' hl

lemma latch_view2_consistent {X1 X2 Y : Type} (cand : View X1 X2 → Option Y)
    (h : ℕ → Signal X1 X2) (target : Y)
    (hcons : ∀ r ≥ 1, ∀ o, cand (view2 (pre h r)) = some o → o = target) :
    ∀ r o, latch cand (view2 (pre h r)) = some o → o = target := by
  intro r
  induction r with
  | zero =>
    intro o ho
    simp [pre, view2, views, latch] at ho
  | succ r ih =>
    intro o ho
    rw [latch_view2_succ] at ho
    cases hl : latch cand (view2 (pre h r)) with
    | none =>
      rw [hl, Option.none_or] at ho
      exact hcons (r + 1) (by omega) o ho
    | some o' =>
      rw [hl, Option.some_or] at ho
      injection ho with heq
      rw [← heq]
      exact ih o' hl

/-! ### Sufficiency (`←`): consensus from a missing point `x ∈ [0, 1] \ π(A)` -/

noncomputable def cutCand {V : Type} (fallback : V) (x : ℝ) (v : View V V) : Option V := by
  classical
  let r := vround v
  exact if r = 0 then none
    else if (vcoord v : ℝ) + 1 < x * (3 : ℝ) ^ r then some (readProp1 fallback v)
    else if x * (3 : ℝ) ^ r < (vcoord v : ℝ) - 1 then some (readProp2 fallback v)
    else none

lemma map_graph_pre {X1 X2 : Type} (h : ℕ → Signal X1 X2) (r : ℕ) :
    (pre h r).map (fun s => s.2.2) = pre (graphOf h) r := by
  apply List.ext_getElem
  · simp [pre]
  · intro i h1 h2; simp [pre, graphOf]

lemma pre_zero_elem {α : Type} (h : ℕ → α) (r : ℕ) (hr : 0 < r) :
    (pre h r)[0]'(by simp [pre, hr]) = h 0 := by
  simp [pre]

lemma cutCand_view_consistent {V : Type} (fallback : V) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (h : ℕ → Signal V V) (r : ℕ) (hr : 1 ≤ r) :
    let target := if piMap (graphOf h) < x then (h 0).1 else (h 0).2.1
    (∀ o, cutCand fallback x (view1 (pre h r)) = some o → o = target) ∧
    (∀ o, cutCand fallback x (view2 (pre h r)) = some o → o = target) := by
  classical
  dsimp only
  have hl : (pre h r).length = r := pre_length_gen h r
  have hlpos : 0 < (pre h r).length := by omega
  have vr := vround_views (pre h r)
  rw [hl] at vr
  have vb := vcoord_bounds (pre h r)
  rw [map_graph_pre] at vb
  have pm := piMap_mul_bounds (graphOf h) r
  have hp : (0 : ℝ) < (3 : ℝ) ^ r := by positivity
  have hr0 : r ≠ 0 := by omega
  have hk1 := readProp1_known fallback (pre h r) hlpos
  have hk2 := readProp2_known fallback (pre h r) hlpos
  have h0_eq : (pre h r)[0]'hlpos = h 0 := pre_zero_elem h r (by omega)
  set j := jIdx (pre (graphOf h) r)
  have hj1_lo : (j : ℝ) ≤ (vcoord (view1 (pre h r)) : ℝ) := by exact_mod_cast vb.1.1
  have hj1_hi : (vcoord (view1 (pre h r)) : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast vb.1.2
  have hj2_lo : (j : ℝ) ≤ (vcoord (view2 (pre h r)) : ℝ) := by exact_mod_cast vb.2.1
  have hj2_hi : (vcoord (view2 (pre h r)) : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast vb.2.2
  constructor
  · intro o ho
    unfold cutCand at ho
    rw [vr.1] at ho
    simp only [hr0, ↓reduceIte] at ho
    split_ifs at ho with hlt hgt
    · injection ho with ho
      have hpw : piMap (graphOf h) < x := by nlinarith [pm.2, hj1_lo, hlt, hp]
      rw [if_pos hpw, ← ho, hk1.1, h0_eq]
    · injection ho with ho
      have hpw : ¬ piMap (graphOf h) < x := by nlinarith [pm.1, hj1_hi, hgt, hp]
      have hvc_pos : 0 < vcoord (view1 (pre h r)) := by
        have : (1 : ℝ) < (vcoord (view1 (pre h r)) : ℝ) := by nlinarith [hx.1, hp, hgt]
        exact_mod_cast (show (0 : ℝ) < (vcoord (view1 (pre h r)) : ℝ) by linarith)
      rw [if_neg hpw, ← ho, hk2.2 hvc_pos, h0_eq]
  · intro o ho
    unfold cutCand at ho
    rw [vr.2] at ho
    simp only [hr0, ↓reduceIte] at ho
    split_ifs at ho with hlt hgt
    · injection ho with ho
      have hpw : piMap (graphOf h) < x := by nlinarith [pm.2, hj2_lo, hlt, hp]
      have hvc_lt : vcoord (view2 (pre h r)) < 3 ^ (pre h r).length := by
        rw [hl]
        have : (vcoord (view2 (pre h r)) : ℝ) < (3 : ℝ) ^ r := by nlinarith [hx.2, hp, hlt]
        exact_mod_cast this
      rw [if_pos hpw, ← ho, hk1.2 hvc_lt, h0_eq]
    · injection ho with ho
      have hpw : ¬ piMap (graphOf h) < x := by nlinarith [pm.1, hj2_hi, hgt, hp]
      rw [if_neg hpw, ← ho, hk2.1, h0_eq]

lemma cutCand_view_terminates {V : Type} (fallback : V) (x : ℝ) (_hx : x ∈ Set.Icc (0 : ℝ) 1)
    (h : ℕ → Signal V V) (hne : piMap (graphOf h) ≠ x) :
    ∃ r ≥ 1,
      (cutCand fallback x (view1 (pre h r))).isSome ∧
      (cutCand fallback x (view2 (pre h r))).isSome := by
  classical
  have hdiff : 0 < |piMap (graphOf h) - x| / 2 :=
    div_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) (by norm_num)
  obtain ⟨m, hm⟩ := hpow (|piMap (graphOf h) - x| / 2) hdiff
  set r := m + 1
  have hr : 1 ≤ r := by omega
  have hr0 : r ≠ 0 := by omega
  have hp_m : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hgap_m : 2 < |piMap (graphOf h) - x| * (3 : ℝ) ^ m := by
    have := (div_lt_iff₀ hp_m).mp (show (1 : ℝ) / (3 : ℝ) ^ m < |piMap (graphOf h) - x| / 2 from hm)
    linarith
  have hgap : 2 < |piMap (graphOf h) - x| * (3 : ℝ) ^ r := by
    have hpow_r : (3 : ℝ) ^ r = 3 * (3 : ℝ) ^ m := by simp [r, pow_succ]; ring
    rw [hpow_r]
    have hnn : 0 ≤ |piMap (graphOf h) - x| := abs_nonneg _
    nlinarith
  have hl : (pre h r).length = r := pre_length_gen h r
  have vr := vround_views (pre h r)
  rw [hl] at vr
  have vb := vcoord_bounds (pre h r)
  rw [map_graph_pre] at vb
  have pm := piMap_mul_bounds (graphOf h) r
  set j := jIdx (pre (graphOf h) r)
  have hj1_lo : (j : ℝ) ≤ (vcoord (view1 (pre h r)) : ℝ) := by exact_mod_cast vb.1.1
  have hj1_hi : (vcoord (view1 (pre h r)) : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast vb.1.2
  have hj2_lo : (j : ℝ) ≤ (vcoord (view2 (pre h r)) : ℝ) := by exact_mod_cast vb.2.1
  have hj2_hi : (vcoord (view2 (pre h r)) : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast vb.2.2
  refine ⟨r, hr, ?_, ?_⟩
  · unfold cutCand
    rw [vr.1]
    simp only [hr0, ↓reduceIte]
    by_cases hside : piMap (graphOf h) < x
    · rw [abs_of_neg (sub_neg.mpr hside)] at hgap
      have hlt : (vcoord (view1 (pre h r)) : ℝ) + 1 < x * (3 : ℝ) ^ r := by
        nlinarith [pm.1, hj1_hi, hgap]
      rw [if_pos hlt]
      rfl
    · have hside' : x < piMap (graphOf h) := lt_of_le_of_ne (le_of_not_gt hside) hne.symm
      rw [abs_of_pos (sub_pos.mpr hside')] at hgap
      have hnlt : ¬ ((vcoord (view1 (pre h r)) : ℝ) + 1 < x * (3 : ℝ) ^ r) := by
        have hp : (0 : ℝ) < (3 : ℝ) ^ r := by positivity
        nlinarith [pm.2, hj1_lo, hside', hp]
      have hgt : x * (3 : ℝ) ^ r < (vcoord (view1 (pre h r)) : ℝ) - 1 := by
        nlinarith [pm.2, hj1_lo, hgap]
      rw [if_neg hnlt, if_pos hgt]
      rfl
  · unfold cutCand
    rw [vr.2]
    simp only [hr0, ↓reduceIte]
    by_cases hside : piMap (graphOf h) < x
    · rw [abs_of_neg (sub_neg.mpr hside)] at hgap
      have hlt : (vcoord (view2 (pre h r)) : ℝ) + 1 < x * (3 : ℝ) ^ r := by
        nlinarith [pm.1, hj2_hi, hgap]
      rw [if_pos hlt]
      rfl
    · have hside' : x < piMap (graphOf h) := lt_of_le_of_ne (le_of_not_gt hside) hne.symm
      rw [abs_of_pos (sub_pos.mpr hside')] at hgap
      have hnlt : ¬ ((vcoord (view2 (pre h r)) : ℝ) + 1 < x * (3 : ℝ) ^ r) := by
        have hp : (0 : ℝ) < (3 : ℝ) ^ r := by positivity
        nlinarith [pm.2, hj2_lo, hside', hp]
      have hgt : x * (3 : ℝ) ^ r < (vcoord (view2 (pre h r)) : ℝ) - 1 := by
        nlinarith [pm.2, hj2_lo, hgap]
      rw [if_neg hnlt, if_pos hgt]
      rfl

lemma consensus_of_ne_Icc {V : Type} [Nonempty V] (A : Set (ℕ → CommGraph))
    (hne : piMap '' A ≠ Set.Icc (0 : ℝ) 1) : ConsensusSolvable V A := by
  classical
  have hex : ∃ x ∈ Set.Icc (0 : ℝ) 1, x ∉ piMap '' A := by
    by_contra h
    have hsub : Set.Icc (0 : ℝ) 1 ⊆ piMap '' A :=
      fun y hy => Classical.not_not.mp fun hm => h ⟨y, hy, hm⟩
    exact hne (Set.Subset.antisymm (range_sub A) hsub)
  obtain ⟨x, hx, hmiss⟩ := hex
  let fallback : V := Classical.choice inferInstance
  let cand := cutCand fallback x
  let f : Algorithm V V (Option V) (Option V) := ⟨latch cand, latch cand⟩
  refine ⟨f, ?_, ?_⟩
  · intro h _ r _
    constructor
    · intro o ho
      change latch cand (view1 (pre h r)) = some o at ho
      change latch cand (view1 (pre h (r + 1))) = some o
      rw [latch_view1_succ, ho]
      rfl
    · intro o ho
      change latch cand (view2 (pre h r)) = some o at ho
      change latch cand (view2 (pre h (r + 1))) = some o
      rw [latch_view2_succ, ho]
      rfl
  · intro h hg
    have hpx : piMap (graphOf h) ≠ x := fun heq => hmiss ⟨graphOf h, hg, heq⟩
    obtain ⟨m, hm1, hs1, hs2⟩ := cutCand_view_terminates fallback x hx h hpx
    let target : V := if piMap (graphOf h) < x then (h 0).1 else (h 0).2.1
    have hcons1 : ∀ k ≥ 1, ∀ o, cand (view1 (pre h k)) = some o → o = target :=
      fun k hk => (cutCand_view_consistent fallback x hx h k hk).1
    have hcons2 : ∀ k ≥ 1, ∀ o, cand (view2 (pre h k)) = some o → o = target :=
      fun k hk => (cutCand_view_consistent fallback x hx h k hk).2
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    obtain ⟨c1, hc1⟩ := Option.isSome_iff_exists.mp hs1
    obtain ⟨c2, hc2⟩ := Option.isSome_iff_exists.mp hs2
    change cand (view1 (pre h (k + 1))) = some c1 at hc1
    change cand (view2 (pre h (k + 1))) = some c2 at hc2
    have h1_some : ∃ o1, latch cand (view1 (pre h (k + 1))) = some o1 := by
      rw [latch_view1_succ, hc1]
      cases latch cand (view1 (pre h k)) <;> exact ⟨_, rfl⟩
    have h2_some : ∃ o2, latch cand (view2 (pre h (k + 1))) = some o2 := by
      rw [latch_view2_succ, hc2]
      cases latch cand (view2 (pre h k)) <;> exact ⟨_, rfl⟩
    obtain ⟨o1, ho1⟩ := h1_some
    obtain ⟨o2, ho2⟩ := h2_some
    have he1 : o1 = target := latch_view1_consistent cand h target hcons1 (k + 1) o1 ho1
    have he2 : o2 = target := latch_view2_consistent cand h target hcons2 (k + 1) o2 ho2
    refine ⟨k + 1, by omega, target, target, ?_, ?_, rfl, ?_⟩
    · exact he1 ▸ ho1
    · exact he2 ▸ ho2
    · dsimp only [target]
      split_ifs <;> simp

/-! ### Necessity (`→`): connectedness and adjacent views on constant proposals -/

def propHist {V : Type} (a b : V) (gs : List CommGraph) : List (Signal V V) :=
  gs.map (fun g => (a, b, g))

def constSig {V : Type} (a b : V) (w : ℕ → CommGraph) : ℕ → Signal V V :=
  fun n => (a, b, w n)

lemma pre_constSig {V : Type} (a b : V) (w : ℕ → CommGraph) (r : ℕ) :
    pre (constSig a b w) r = propHist a b (pre w r) := by
  apply List.ext_getElem
  · simp [pre, propHist]
  · intro i h1 h2; simp [pre, constSig, propHist]

lemma list_snoc {α : Type} (l : List α) (hl : l ≠ []) : ∃ init last, l = init ++ [last] := by
  induction l using List.reverseRecOn with
  | nil => contradiction
  | append_singleton init last _ => exact ⟨init, last, rfl⟩

lemma adj_propHist {V : Type} (a b : V) :
    ∀ (r : ℕ) (gs1 gs2 : List CommGraph),
      gs1.length = r → gs2.length = r → jIdx gs1 + 1 = jIdx gs2 →
      if (jIdx gs1) % 2 = 0 then view2 (propHist a b gs1) = view2 (propHist a b gs2)
      else view1 (propHist a b gs1) = view1 (propHist a b gs2)
  | 0, gs1, gs2, h1, h2, hnext => by
      have e1 : gs1 = [] := List.eq_nil_of_length_eq_zero h1
      have e2 : gs2 = [] := List.eq_nil_of_length_eq_zero h2
      subst e1; subst e2
      simp [jIdx] at hnext
  | r + 1, gs1, gs2, h1, h2, hnext => by
      obtain ⟨u1, g1, rfl⟩ := list_snoc gs1 (by intro e; simp [e] at h1)
      obtain ⟨u2, g2, rfl⟩ := list_snoc gs2 (by intro e; simp [e] at h2)
      have hu1 : u1.length = r := by simp at h1; exact h1
      have hu2 : u2.length = r := by simp at h2; exact h2
      rw [jIdx_append, jIdx_append] at hnext
      rw [jIdx_append]
      set k1 := jIdx u1
      set k2 := jIdx u2
      have hb1 := stepJ_bounds k1 g1
      have hb2 := stepJ_bounds k2 g2
      have hcases : k1 = k2 ∨ k1 + 1 = k2 := by omega
      have hv1_step : ∀ u g, view1 (propHist a b (u ++ [g])) =
          (viewStep (view1 (propHist a b u), view2 (propHist a b u)) (a, b, g)).1 := by
        intro u g; simp [propHist, view1, view2, views]
      have hv2_step : ∀ u g, view2 (propHist a b (u ++ [g])) =
          (viewStep (view1 (propHist a b u), view2 (propHist a b u)) (a, b, g)).2 := by
        intro u g; simp [propHist, view1, view2, views]
      rcases hcases with hk | hk
      · have hu_eq : u1 = u2 := inj_list u1 u2 (hu1.trans hu2.symm) hk
        subst hu_eq
        rw [← hk] at hnext
        by_cases he : k1 % 2 = 0
        · cases g1 <;> cases g2 <;> simp only [stepJ, he, ↓reduceIte, delta] at hnext ⊢
          all_goals try omega
          all_goals
            split_ifs <;> try omega
            all_goals simp [hv1_step, hv2_step, viewStep]
        · cases g1 <;> cases g2 <;> simp only [stepJ, he, ↓reduceIte, delta] at hnext ⊢
          all_goals try omega
          all_goals
            split_ifs <;> try omega
            all_goals simp [hv1_step, hv2_step, viewStep]
      · have ih_res := adj_propHist a b r u1 u2 hu1 hu2 hk
        change (if k1 % 2 = 0 then _ else _) at ih_res
        by_cases he : k1 % 2 = 0
        · have he2 : ¬ (k2 % 2 = 0) := by omega
          simp only [he, ↓reduceIte] at ih_res
          cases g1 <;> cases g2 <;>
            simp only [stepJ, he, he2, ↓reduceIte, delta] at hnext ⊢
          all_goals try omega
          split_ifs with hpar
          · rw [hv2_step, hv2_step]
            simp [viewStep, ih_res]
          · omega
        · have he2 : k2 % 2 = 0 := by omega
          simp only [he, ↓reduceIte] at ih_res
          cases g1 <;> cases g2 <;>
            simp only [stepJ, he, he2, ↓reduceIte, delta] at hnext ⊢
          all_goals try omega
          split_ifs with hpar
          · omega
          · rw [hv1_step, hv1_step]
            simp [viewStep, ih_res]

lemma near_shares_view {V : Type} (a b : V) (w1 w2 : ℕ → CommGraph) (r : ℕ)
    (hnear : |piMap w1 - piMap w2| < 1 / (3 : ℝ) ^ r) :
    view1 (pre (constSig a b w1) r) = view1 (pre (constSig a b w2) r) ∨
      view2 (pre (constSig a b w1) r) = view2 (pre (constSig a b w2) r) := by
  rw [pre_constSig, pre_constSig]
  have pm1 := piMap_mul_bounds w1 r
  have pm2 := piMap_mul_bounds w2 r
  have hp : (0 : ℝ) < (3 : ℝ) ^ r := by positivity
  have hnear_mul : |piMap w1 - piMap w2| * (3 : ℝ) ^ r < 1 :=
    (lt_div_iff₀ hp).mp hnear
  rw [abs_sub_lt_iff] at hnear
  have h1 : (piMap w1 - piMap w2) * (3 : ℝ) ^ r < 1 := by
    have := (lt_div_iff₀ hp).mp hnear.1
    linarith
  have h2 : (piMap w2 - piMap w1) * (3 : ℝ) ^ r < 1 := by
    have := (lt_div_iff₀ hp).mp hnear.2
    linarith
  set j1 := jIdx (pre w1 r)
  set j2 := jIdx (pre w2 r)
  have hj12 : (j1 : ℝ) < (j2 : ℝ) + 2 := by nlinarith [pm1.1, pm2.2, h1]
  have hj21 : (j2 : ℝ) < (j1 : ℝ) + 2 := by nlinarith [pm2.1, pm1.2, h2]
  have hn12 : j1 < j2 + 2 := by exact_mod_cast hj12
  have hn21 : j2 < j1 + 2 := by exact_mod_cast hj21
  have htri : j1 = j2 ∨ j1 + 1 = j2 ∨ j2 + 1 = j1 := by omega
  rcases htri with heq | h12 | h21
  · have hpre := inj_list (pre w1 r) (pre w2 r) (by simp [pre_length_gen]) heq
    left; rw [hpre]
  · have hadj := adj_propHist a b r (pre w1 r) (pre w2 r) (pre_length_gen w1 r) (pre_length_gen w2 r) h12
    split_ifs at hadj
    · exact Or.inr hadj
    · exact Or.inl hadj
  · have hadj := adj_propHist a b r (pre w2 r) (pre w1 r) (pre_length_gen w2 r) (pre_length_gen w1 r) h21
    split_ifs at hadj
    · exact Or.inr hadj.symm
    · exact Or.inl hadj.symm

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

lemma solves_common {V : Type} {f : Algorithm V V (Option V) (Option V)}
    {A : Set (ℕ → CommGraph)} (hf : Solves (consensus V) f A)
    (h : ℕ → Signal V V) (hg : graphOf h ∈ A) :
    ∃ (v : V) (r : ℕ), 1 ≤ r ∧
      outAt1 f h r = some v ∧ outAt2 f h r = some v ∧
      (v = (h 0).1 ∨ v = (h 0).2.1) ∧
      ∀ k ≥ 1, ∀ o : V,
        (outAt1 f h k = some o → o = v) ∧ (outAt2 f h k = some o → o = v) := by
  obtain ⟨r, hr, o1, o2, ho1, ho2, heq, hval⟩ := hf.2 h hg
  dsimp only at heq hval
  subst heq
  refine ⟨o1, r, hr, ho1, ho2, hval, ?_⟩
  intro k hk o
  constructor
  · intro hk1
    have hp1 := (solves_persist hf hg hk (le_max_left k r) o).1 hk1
    have hp2 := (solves_persist hf hg hr (le_max_right k r) o1).1 ho1
    exact Option.some.inj (hp1.symm.trans hp2)
  · intro hk2
    have hp1 := (solves_persist hf hg hk (le_max_left k r) o).2 hk2
    have hp2 := (solves_persist hf hg hr (le_max_right k r) o1).2 ho2
    exact Option.some.inj (hp1.symm.trans hp2)

lemma jIdx_replicate_oneToTwo (r : ℕ) :
    jIdx (List.replicate r .oneToTwo) = 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [List.replicate_succ', jIdx_append, ih]
    rfl

lemma jIdx_replicate_twoToOne (r : ℕ) :
    jIdx (List.replicate r .twoToOne) = 3 ^ r - 1 ∧ (3 ^ r - 1) % 2 = 0 := by
  induction r with
  | zero => simp [jIdx]
  | succ r ih =>
    have h1 : 1 ≤ 3 ^ r := Nat.one_le_pow r 3 (by norm_num)
    rw [List.replicate_succ', jIdx_append, ih.1]
    simp only [stepJ, ih.2, ↓reduceIte, delta, pow_succ]
    omega

lemma pre_eq_replicate_oneToTwo (w : ℕ → CommGraph) (hw : piMap w = 0) (r : ℕ) :
    pre w r = List.replicate r .oneToTwo := by
  have hm := (piMap_mul_bounds w r).1
  rw [hw, zero_mul] at hm
  have hj0 : jIdx (pre w r) = 0 := by
    have : jIdx (pre w r) ≤ 0 := by exact_mod_cast hm
    omega
  exact inj_list _ _ (by simp [pre_length_gen]) (hj0.trans (jIdx_replicate_oneToTwo r).symm)

lemma pre_eq_replicate_twoToOne (w : ℕ → CommGraph) (hw : piMap w = 1) (r : ℕ) :
    pre w r = List.replicate r .twoToOne := by
  have hm := (piMap_mul_bounds w r).2
  rw [hw, one_mul] at hm
  have hlt := jIdx_lt (pre w r)
  rw [pre_length_gen] at hlt
  have hge : 3 ^ r ≤ jIdx (pre w r) + 1 := by exact_mod_cast hm
  have hj : jIdx (pre w r) = 3 ^ r - 1 := by omega
  exact inj_list _ _ (by simp [pre_length_gen]) (hj.trans (jIdx_replicate_twoToOne r).1.symm)

lemma view1_replicate_oneToTwo {V : Type} (a b1 b2 : V) (r : ℕ) :
    view1 (propHist a b1 (List.replicate r .oneToTwo)) =
      view1 (propHist a b2 (List.replicate r .oneToTwo)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have hstep : ∀ b, view1 (propHist a b (List.replicate (r + 1) .oneToTwo)) =
        View.N1 a (view1 (propHist a b (List.replicate r .oneToTwo))) := by
      intro b
      rw [List.replicate_succ', propHist, List.map_append, List.map_singleton]
      simp [propHist, view1, views, viewStep]
    rw [hstep, hstep, ih]

lemma view2_replicate_twoToOne {V : Type} (a1 a2 b : V) (r : ℕ) :
    view2 (propHist a1 b (List.replicate r .twoToOne)) =
      view2 (propHist a2 b (List.replicate r .twoToOne)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have hstep : ∀ a, view2 (propHist a b (List.replicate (r + 1) .twoToOne)) =
        View.N2 b (view2 (propHist a b (List.replicate r .twoToOne))) := by
      intro a
      rw [List.replicate_succ', propHist, List.map_append, List.map_singleton]
      simp [propHist, view2, views, viewStep]
    rw [hstep, hstep, ih]

end DistLTLSynth.Char.Lemma31Aux

open DistLTLSynth.Char DistLTLSynth.Char.Lemma31Aux in
theorem solution (V : Type) [Fintype V] [DecidableEq V] (hV : 2 ≤ Fintype.card V)
    (A : Set (ℕ → CommGraph)) :
    ConsensusSolvable V A ↔ piMap '' A ≠ Set.Icc (0 : ℝ) 1 := by
  classical
  constructor
  · rintro ⟨f, hf⟩ hfull
    obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp (show 1 < Fintype.card V by omega)
    have hpreimg : ∀ t : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}, ∃ w ∈ A, piMap w = t.val :=
      fun t => (Set.ext_iff.mp hfull.symm t.val).mp t.property
    choose w hwA hw_pi using hpreimg
    have hdec : ∀ t : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1},
        ∃ (v : V) (r : ℕ), 1 ≤ r ∧
          outAt1 f (constSig a b (w t)) r = some v ∧
          outAt2 f (constSig a b (w t)) r = some v ∧
          (v = a ∨ v = b) ∧
          ∀ k ≥ 1, ∀ o : V,
            (outAt1 f (constSig a b (w t)) k = some o → o = v) ∧
            (outAt2 f (constSig a b (w t)) k = some o → o = v) :=
      fun t => solves_common hf (constSig a b (w t)) (hwA t)
    choose val rnd hrnd hout1 hout2 _ hcons using hdec
    let t0 : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} := ⟨0, by norm_num⟩
    let t1 : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} := ⟨1, by norm_num⟩
    have hloc : ∀ t t' : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1},
        |t'.val - t.val| < 1 / (3 : ℝ) ^ (rnd t) → val t' = val t := by
      intro t t' hdist
      have hnear : |piMap (w t) - piMap (w t')| < 1 / (3 : ℝ) ^ (rnd t) := by
        rw [hw_pi t, hw_pi t', abs_sub_comm]
        exact hdist
      rcases near_shares_view a b (w t) (w t') (rnd t) hnear with hv1 | hv2
      · have ho : outAt1 f (constSig a b (w t')) (rnd t) = some (val t) := by
          unfold outAt1 at hout1 ⊢
          rw [← hv1]
          exact hout1 t
        exact ((hcons t' (rnd t) (hrnd t) (val t)).1 ho).symm
      · have ho : outAt2 f (constSig a b (w t')) (rnd t) = some (val t) := by
          unfold outAt2 at hout2 ⊢
          rw [← hv2]
          exact hout2 t
        exact ((hcons t' (rnd t) (hrnd t) (val t)).2 ho).symm
    -- Extreme `t = 0`: `val t0 = a`
    have hval0 : val t0 = a := by
      obtain ⟨v0, r0, hr0, h0_out1, _, h0_ab, _⟩ :=
        solves_common hf (constSig a a (w t0)) (hwA t0)
      have hv0 : v0 = a := h0_ab.elim id id
      rw [hv0] at h0_out1
      have hsame_view : view1 (pre (constSig a b (w t0)) r0) =
          view1 (pre (constSig a a (w t0)) r0) := by
        rw [pre_constSig, pre_constSig, pre_eq_replicate_oneToTwo (w t0) (hw_pi t0) r0]
        exact view1_replicate_oneToTwo a b a r0
      have ho : outAt1 f (constSig a b (w t0)) r0 = some a := by
        unfold outAt1 at h0_out1 ⊢
        rw [hsame_view]
        exact h0_out1
      exact ((hcons t0 r0 hr0 a).1 ho).symm
    -- Extreme `t = 1`: `val t1 = b`
    have hval1 : val t1 = b := by
      obtain ⟨v1, r1, hr1, _, h1_out2, h1_bb, _⟩ :=
        solves_common hf (constSig b b (w t1)) (hwA t1)
      have hv1 : v1 = b := h1_bb.elim id id
      rw [hv1] at h1_out2
      have hsame_view : view2 (pre (constSig a b (w t1)) r1) =
          view2 (pre (constSig b b (w t1)) r1) := by
        rw [pre_constSig, pre_constSig, pre_eq_replicate_twoToOne (w t1) (hw_pi t1) r1]
        exact view2_replicate_twoToOne a b b r1
      have ho : outAt2 f (constSig a b (w t1)) r1 = some b := by
        unfold outAt2 at h1_out2 ⊢
        rw [hsame_view]
        exact h1_out2
      exact ((hcons t1 r1 hr1 b).2 ho).symm
    -- Connectedness of `Icc 0 1`
    let U : Set ℝ :=
      ⋃ (t : {t : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} // val t = a}),
        Metric.ball t.1.val (1 / (3 : ℝ) ^ (rnd t.1))
    let W : Set ℝ :=
      ⋃ (t : {t : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} // val t ≠ a}),
        Metric.ball t.1.val (1 / (3 : ℝ) ^ (rnd t.1))
    have hU : IsOpen U := isOpen_iUnion (fun _ => Metric.isOpen_ball)
    have hW : IsOpen W := isOpen_iUnion (fun _ => Metric.isOpen_ball)
    have hcov : Set.Icc (0 : ℝ) 1 ⊆ U ∪ W := by
      intro x hx
      let tx : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} := ⟨x, hx⟩
      have hrad : 0 < 1 / (3 : ℝ) ^ (rnd tx) := by positivity
      by_cases hvx : val tx = a
      · left
        exact Set.mem_iUnion.mpr ⟨⟨tx, hvx⟩, Metric.mem_ball_self hrad⟩
      · right
        exact Set.mem_iUnion.mpr ⟨⟨tx, hvx⟩, Metric.mem_ball_self hrad⟩
    have h0_mem : (Set.Icc (0 : ℝ) 1 ∩ U).Nonempty := by
      refine ⟨0, t0.property, Set.mem_iUnion.mpr ⟨⟨t0, hval0⟩, ?_⟩⟩
      exact Metric.mem_ball_self (by positivity)
    have h1_mem : (Set.Icc (0 : ℝ) 1 ∩ W).Nonempty := by
      refine ⟨1, t1.property, Set.mem_iUnion.mpr ⟨⟨t1, ?_⟩, ?_⟩⟩
      · rw [hval1]; exact hab.symm
      · exact Metric.mem_ball_self (by positivity)
    obtain ⟨z, hzIcc, hzU, hzW⟩ := isPreconnected_Icc U W hU hW hcov h0_mem h1_mem
    obtain ⟨⟨tu, htu⟩, hzu⟩ := Set.mem_iUnion.mp hzU
    obtain ⟨⟨tw, htw⟩, hzw⟩ := Set.mem_iUnion.mp hzW
    rw [Metric.mem_ball, Real.dist_eq] at hzu hzw
    let tz : {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} := ⟨z, hzIcc⟩
    have hza : val tz = a := (hloc tu tz hzu).trans htu
    have hzna : val tz ≠ a := by
      rw [hloc tw tz hzw]
      exact htw
    exact hzna hza
  · intro hne
    have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    exact consensus_of_ne_Icc A hne
