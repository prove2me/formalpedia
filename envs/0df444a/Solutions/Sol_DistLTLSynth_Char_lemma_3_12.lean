-- Prove2me | solution 1 for DistLTLSynth.Char.lemma_3_12
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T12:45:58.894242+00:00
-- url     : https://prove2.me/submissions/e13c9b0d-9bb6-4ed9-bf51-31933072e58a

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL
import Definitions.Def_DistLTLSynth_Char_Geometric
import Definitions.Def_DistLTLSynth_Char_Automata
import Definitions.Def_DistLTLSynth_Char_Consensus
import Definitions.Def_DistLTLSynth_Char_ComponentTree
import Definitions.Def_DistLTLSynth_Char_SynthesisEngine
import Definitions.Def_DistLTLSynth_Char_SymbolicArena
import Theorems.Thm_DistLTLSynth_Char_lemma_3_13

set_option autoImplicit false

namespace DistLTLSynth.Char.Lemma312Aux

open DistLTLSynth.Char

lemma mem_validSymLabels_iff (c : SymCtx) (pa : SymPosCode × SymActCode) :
    pa ∈ validSymLabels c ↔
      pa.1 ∈ allSymPos c ∧ pa.2 ∈ allSymActsFor c pa.1 ∧ actValid c pa.1 pa.2 = true :=
  DistLTLSynth.Char.lemma_3_13.2.2.2.2.2.1 c pa

lemma tsRootOk_buildTreeSpec (E : Thm34Engine) (c : SymCtx)
    (a : Fin ((buildTreeSpec E c).2.1 + 1)) :
    tsRootOk (buildTreeSpec E c) a =
      if a.val = 0 then false
      else decide (((validSymLabels c).getD (a.val - 1) (initSymPos, ([], [], []))).1 = initSymPos) :=
  DistLTLSynth.Char.lemma_3_13.2.2.2.2.2.2.2.2.2.1 E c a

lemma tsChildOk_buildTreeSpec (E : Thm34Engine) (c : SymCtx)
    (a : Fin ((buildTreeSpec E c).2.1 + 1))
    (d : Fin ((buildTreeSpec E c).1 + 1))
    (a' : Fin ((buildTreeSpec E c).2.1 + 1)) :
    tsChildOk (buildTreeSpec E c) a d a' =
      if a.val = 0 then decide (a'.val = 0)
      else
        let pa := (validSymLabels c).getD (a.val - 1) (initSymPos, ([], [], []))
        let comps := symComponents E c pa.1 pa.2
        if d.val < comps.length then
          if a'.val = 0 then false
          else
            let pa' := (validSymLabels c).getD (a'.val - 1) (initSymPos, ([], [], []))
            decide (pa'.1 = childSymPos (ctxI c) pa.1 (comps.getD d.val []))
        else decide (a'.val = 0) :=
  DistLTLSynth.Char.lemma_3_13.2.2.2.2.2.2.2.2.2.2.1 E c a d a'

lemma tsDPA_buildTreeSpec_accepts_iff (E : Thm34Engine) (c : SymCtx)
    (ad : ℕ → Fin ((buildTreeSpec E c).2.1 + 1) × Fin ((buildTreeSpec E c).1 + 1)) :
    (tsDPA (buildTreeSpec E c)).Accepts ad ↔
      ¬ ∃ (iSeq : ℕ → Fin (ctxBFull c)) (pSeq : ℕ → Fin (maxList (ctxBCode c).2.2 + 1)),
        (iSeq 0).val = 0 ∧
        (∀ n, edgeStepOk E c (validSymLabels c) (ad n).1.val (ad n).2.val
          (iSeq n).val (pSeq n).val (iSeq (n + 1)).val = true) ∧
        OddParityCond (fun n => (pSeq n).val) :=
  DistLTLSynth.Char.lemma_3_13.2.2.2.2.2.2.2.2.2.2.2.1 E c ad

lemma mem_symLiveExts_iff (E : Thm34Engine) (ctx : SymCtx) (pos : SymPosCode) (act : SymActCode)
    (e : SymExtElem) :
    e ∈ symLiveExts E ctx pos act ↔
      e.1 ∈ fixedIdxs pos act ∧
      e.2.1 ∈ fullBlocks (ctxI ctx) (ctxD ctx) ∧
      e.2.2 = symNextState E ctx pos act e.1 e.2.1 ∧
      (ctxLive ctx).getD e.2.2 false = true :=
  DistLTLSynth.Char.lemma_3_13.2.2.2.2.2.2.2.2.2.2.2.2.1 E ctx pos act e

lemma symComponents_props (E : Thm34Engine) (ctx : SymCtx)
    (pos : SymPosCode) (act : SymActCode)
    (hfix_le : (fixedIdxs pos act).length ≤ ctxBRed ctx) :
    let S := symLiveExts E ctx pos act
    let comps := symComponents E ctx pos act
    comps.length ≤ ctxBFull ctx ∧
    ∀ (d : ℕ) (hd : d < comps.length),
      let comp := comps[d]'hd
      1 ≤ comp.length ∧ comp.length ≤ ctxBFull ctx ∧ comp.Nodup ∧
      (∀ e ∈ comp, e ∈ S) ∧
      ((∀ a ∈ S, ∀ b ∈ S, symExtAdj (ctxI ctx) pos a b = symExtAdj (ctxI ctx) pos b a) →
        ∀ j1 j2 : Fin comp.length,
          Relation.ReflTransGen
            (fun x y : Fin comp.length => symExtAdj (ctxI ctx) pos comp[x] comp[y] = true) j1 j2) :=
  DistLTLSynth.Char.lemma_3_13.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 E ctx pos act hfix_le

lemma extEqFrom_exact (I : Instance) {h1 h2 : List (Signal I.X1 I.X2)} (hlen : h1.length = h2.length)
    (w1 w2 : List ℕ) :
    extEqFrom I (decide (view1 h1 = view1 h2)) (decide (view2 h1 = view2 h2)) w1 w2 =
      (decide (view1 (h1 ++ decHist I w1) = view1 (h2 ++ decHist I w2)),
       decide (view2 (h1 ++ decHist I w1) = view2 (h2 ++ decHist I w2))) :=
  DistLTLSynth.Char.lemma_3_13.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 I hlen w1 w2

lemma mem_wordsOf_iff {α : Type} (choices : List α) (n : ℕ) (w : List α) :
    w ∈ wordsOf choices n ↔ w.length = n ∧ ∀ a ∈ w, a ∈ choices := by
  rw [wordsOf, List.mem_sections, List.forall₂_iff_get]
  simp only [List.length_map, List.length_range]
  constructor
  · rintro ⟨hlen, hget⟩
    refine ⟨hlen, fun a ha => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    simpa using hget i hi (by simpa [hlen] using hi)
  · rintro ⟨hlen, hall⟩
    refine ⟨hlen, fun i hi _ => ?_⟩
    simpa using hall w[i] (List.getElem_mem hi)

lemma view1_append_singleton {X1 X2 : Type} (l : List (Signal X1 X2)) (s : Signal X1 X2) :
    view1 (l ++ [s]) = (viewStep (view1 l, view2 l) s).1 := by
  simp [view1, view2, views]

lemma view2_append_singleton {X1 X2 : Type} (l : List (Signal X1 X2)) (s : Signal X1 X2) :
    view2 (l ++ [s]) = (viewStep (view1 l, view2 l) s).2 := by
  simp [view1, view2, views]

lemma vdepth_views {X1 X2 : Type} (l : List (Signal X1 X2)) :
    vdepth (view1 l) = l.length ∧ vdepth (view2 l) = l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [view1, view2, views, vdepth]
  | append_singleton l s ih =>
    rcases s with ⟨x1, x2, g⟩
    rw [view1_append_singleton, view2_append_singleton]
    cases g <;> simp [viewStep, vdepth, ih.1, ih.2]

lemma vdepth_viewOf {X1 X2 : Type} (p : Proc) (l : List (Signal X1 X2)) :
    vdepth (viewOf p l) = l.length := by
  cases p
  · exact (vdepth_views l).1
  · exact (vdepth_views l).2

lemma parentView_append_singleton {X1 X2 : Type} (p : Proc) (l : List (Signal X1 X2)) (s : Signal X1 X2) :
    parentView (viewOf p (l ++ [s])) = viewOf p l := by
  rcases s with ⟨x1, x2, g⟩
  cases p <;> simp only [viewOf, view1_append_singleton, view2_append_singleton] <;>
    cases g <;> rfl

lemma iterParent_append {X1 X2 : Type} (p : Proc) (a u : List (Signal X1 X2)) :
    iterParent u.length (viewOf p (a ++ u)) = viewOf p a := by
  induction u using List.reverseRecOn with
  | nil => simp [iterParent]
  | append_singleton u s ih =>
    rw [List.length_append, List.length_singleton, ← List.append_assoc]
    change iterParent u.length (parentView (viewOf p ((a ++ u) ++ [s]))) = viewOf p a
    rw [parentView_append_singleton, ih]

lemma viewOf_prefix_eq {X1 X2 : Type} {p : Proc} {a1 a2 u1 u2 : List (Signal X1 X2)}
    (hlen : a1.length = a2.length)
    (heq : viewOf p (a1 ++ u1) = viewOf p (a2 ++ u2)) :
    u1.length = u2.length ∧ viewOf p a1 = viewOf p a2 := by
  have hd := congrArg vdepth heq
  rw [vdepth_viewOf, vdepth_viewOf, List.length_append, List.length_append, hlen] at hd
  have hu : u1.length = u2.length := by omega
  refine ⟨hu, ?_⟩
  have hp := congrArg (iterParent u1.length) heq
  rw [iterParent_append] at hp
  rw [hu, iterParent_append] at hp
  exact hp

lemma views_injective {X1 X2 : Type} {h1 h2 : List (Signal X1 X2)}
    (h_v1 : view1 h1 = view1 h2) (h_v2 : view2 h1 = view2 h2) : h1 = h2 := by
  have hlen : h1.length = h2.length := by
    have := congrArg vdepth h_v1
    rwa [vdepth_views h1 |>.1, vdepth_views h2 |>.1] at this
  induction h1 using List.reverseRecOn generalizing h2 with
  | nil => exact (List.eq_nil_of_length_eq_zero hlen.symm).symm
  | append_singleton l1 s1 ih =>
    cases h2 using List.reverseRecOn with
    | nil => simp at hlen
    | append_singleton l2 s2 =>
      have hp1 : view1 l1 = view1 l2 :=
        (parentView_append_singleton .one l1 s1).symm.trans
          ((congrArg parentView h_v1).trans (parentView_append_singleton .one l2 s2))
      have hp2 : view2 l1 = view2 l2 :=
        (parentView_append_singleton .two l1 s1).symm.trans
          ((congrArg parentView h_v2).trans (parentView_append_singleton .two l2 s2))
      have hl_eq : l1 = l2 := ih hp1 hp2 (by simpa using hlen)
      subst hl_eq
      rw [view1_append_singleton, view1_append_singleton] at h_v1
      rw [view2_append_singleton, view2_append_singleton] at h_v2
      rcases s1 with ⟨x1, x2, g1⟩
      rcases s2 with ⟨x1', x2', g2⟩
      cases g1 <;> cases g2 <;> simp_all [viewStep]

lemma viewStep1_eq_ite {X1 X2 : Type} [DecidableEq CommGraph]
    (uv : View X1 X2 × View X1 X2) (x1 : X1) (x2 : X2) (g : CommGraph) :
    (viewStep uv (x1, x2, g)).1 =
      if g = .oneToTwo then .N1 x1 uv.1 else .C1 x1 uv.1 x2 uv.2 := by
  cases g <;> simp [viewStep]

lemma viewStep2_eq_ite {X1 X2 : Type} [DecidableEq CommGraph]
    (uv : View X1 X2 × View X1 X2) (x1 : X1) (x2 : X2) (g : CommGraph) :
    (viewStep uv (x1, x2, g)).2 =
      if g = .twoToOne then .N2 x2 uv.2 else .C2 x2 uv.2 x1 uv.1 := by
  cases g <;> simp [viewStep]

lemma view_extension {X1 X2 : Type} {a1 a2 b1 b2 : List (Signal X1 X2)}
    (hbase : ∀ p : Proc, viewOf p a1 = viewOf p a2 → viewOf p b1 = viewOf p b2)
    {u1 u2 : List (Signal X1 X2)} (hu : u1.length = u2.length) :
    ∀ p : Proc, viewOf p (a1 ++ u1) = viewOf p (a2 ++ u2) →
      viewOf p (b1 ++ u1) = viewOf p (b2 ++ u2) := by
  induction u1 using List.reverseRecOn generalizing u2 with
  | nil =>
    have hu2 : u2 = [] := List.eq_nil_of_length_eq_zero hu.symm
    subst hu2; simpa using hbase
  | append_singleton w1 s1 ih =>
    cases u2 using List.reverseRecOn with
    | nil => simp at hu
    | append_singleton w2 s2 =>
      have hw : w1.length = w2.length := by simpa using hu
      rcases s1 with ⟨x1, x2, g1⟩
      rcases s2 with ⟨x1', x2', g2⟩
      intro p heq
      simp only [← List.append_assoc] at heq ⊢
      cases p with
      | one =>
        simp only [viewOf, view1_append_singleton, viewStep1_eq_ite] at heq ⊢
        by_cases hg1 : g1 = .oneToTwo <;> by_cases hg2 : g2 = .oneToTwo
        · rw [if_pos hg1, if_pos hg2] at heq ⊢
          rcases View.N1.inj heq with ⟨hx1, hv1⟩
          exact congrArg₂ View.N1 hx1 (ih hw .one hv1)
        · rw [if_pos hg1, if_neg hg2] at heq
          simp at heq
        · rw [if_neg hg1, if_pos hg2] at heq
          simp at heq
        · rw [if_neg hg1, if_neg hg2] at heq ⊢
          rcases View.C1.inj heq with ⟨hx1, hv1, hx2, hv2⟩
          rw [hx1, hx2, show view1 (b1 ++ w1) = view1 (b2 ++ w2) from ih hw .one hv1,
            show view2 (b1 ++ w1) = view2 (b2 ++ w2) from ih hw .two hv2]
      | two =>
        simp only [viewOf, view2_append_singleton, viewStep2_eq_ite] at heq ⊢
        by_cases hg1 : g1 = .twoToOne <;> by_cases hg2 : g2 = .twoToOne
        · rw [if_pos hg1, if_pos hg2] at heq ⊢
          rcases View.N2.inj heq with ⟨hx2, hv2⟩
          exact congrArg₂ View.N2 hx2 (ih hw .two hv2)
        · rw [if_pos hg1, if_neg hg2] at heq
          simp at heq
        · rw [if_neg hg1, if_pos hg2] at heq
          simp at heq
        · rw [if_neg hg1, if_neg hg2] at heq ⊢
          rcases View.C2.inj heq with ⟨hx2, hv2, hx1, hv1⟩
          rw [hx2, hx1, show view2 (b1 ++ w1) = view2 (b2 ++ w2) from ih hw .two hv2,
            show view1 (b1 ++ w1) = view1 (b2 ++ w2) from ih hw .one hv1]

def silentAge {X1 X2 : Type} : View X1 X2 → ℕ
  | .I1 => 0
  | .I2 => 0
  | .N1 _ u => silentAge u + 1
  | .N2 _ v => silentAge v + 1
  | .C1 _ _ _ _ => 0
  | .C2 _ _ _ _ => 0

lemma recent_comm_prefix_eq {X1 X2 : Type} {p : Proc} {a1 a2 u1 u2 : List (Signal X1 X2)}
    (ha : a1.length = a2.length) (hu : u1.length = u2.length)
    (heq : viewOf p (a1 ++ u1) = viewOf p (a2 ++ u2))
    (hrec : silentAge (viewOf p (a1 ++ u1)) < u1.length) :
    a1 = a2 := by
  induction u1 using List.reverseRecOn generalizing u2 with
  | nil => simp at hrec
  | append_singleton w1 s1 ih =>
    cases u2 using List.reverseRecOn with
    | nil => simp at hu
    | append_singleton w2 s2 =>
      have hw : w1.length = w2.length := by simpa using hu
      rcases s1 with ⟨x1, x2, g1⟩
      rcases s2 with ⟨x1', x2', g2⟩
      simp only [← List.append_assoc] at heq hrec
      cases p with
      | one =>
        simp only [viewOf, view1_append_singleton, viewStep1_eq_ite] at heq hrec
        by_cases hg1 : g1 = .oneToTwo <;> by_cases hg2 : g2 = .oneToTwo
        · rw [if_pos hg1, if_pos hg2] at heq
          rw [if_pos hg1] at hrec
          simp only [silentAge, List.length_append, List.length_singleton] at hrec
          rcases View.N1.inj heq with ⟨_, hv1⟩
          have ih' : silentAge (view1 (a1 ++ w1)) < w1.length → a1 = a2 := ih hw hv1
          exact ih' (by omega)
        · rw [if_pos hg1, if_neg hg2] at heq
          simp at heq
        · rw [if_neg hg1, if_pos hg2] at heq
          simp at heq
        · rw [if_neg hg1, if_neg hg2] at heq
          rcases View.C1.inj heq with ⟨_, hv1, _, hv2⟩
          have hfull := views_injective hv1 hv2
          have htake := congrArg (List.take a1.length) hfull
          rwa [List.take_left, ha, List.take_left] at htake
      | two =>
        simp only [viewOf, view2_append_singleton, viewStep2_eq_ite] at heq hrec
        by_cases hg1 : g1 = .twoToOne <;> by_cases hg2 : g2 = .twoToOne
        · rw [if_pos hg1, if_pos hg2] at heq
          rw [if_pos hg1] at hrec
          simp only [silentAge, List.length_append, List.length_singleton] at hrec
          rcases View.N2.inj heq with ⟨_, hv2⟩
          have ih' : silentAge (view2 (a1 ++ w1)) < w1.length → a1 = a2 := ih hw hv2
          exact ih' (by omega)
        · rw [if_pos hg1, if_neg hg2] at heq
          simp at heq
        · rw [if_neg hg1, if_pos hg2] at heq
          simp at heq
        · rw [if_neg hg1, if_neg hg2] at heq
          rcases View.C2.inj heq with ⟨_, hv2, _, hv1⟩
          have hfull := views_injective hv1 hv2
          have htake := congrArg (List.take a1.length) hfull
          rwa [List.take_left, ha, List.take_left] at htake

def ownerInit {V1 V2 X1 X2 : Type} (i1 : View V1 V2) (i2 : View V1 V2) : View X1 X2 → View V1 V2
  | .I1 | .N1 _ _ | .C1 _ _ _ _ => i1
  | .I2 | .N2 _ _ | .C2 _ _ _ _ => i2

lemma ownerInit_viewOf {V1 V2 X1 X2 : Type} (i1 i2 : View V1 V2) (l : List (Signal X1 X2)) :
    ownerInit i1 i2 (view1 l) = i1 ∧ ownerInit i1 i2 (view2 l) = i2 := by
  cases l using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl⟩
  | append_singleton l s =>
    rcases s with ⟨x1, x2, g⟩
    rw [view1_append_singleton, view2_append_singleton]
    cases g <;> exact ⟨rfl, rfl⟩

def simPropView {X1 X2 : Type} (b1 b2 : Bool) : ℕ → View X1 X2 → View Bool Bool
  | 0, v => ownerInit .I1 .I2 v
  | _ + 1, .I1 => .I1
  | _ + 1, .I2 => .I2
  | k + 1, .N1 _ u => .N1 b1 (simPropView b1 b2 k u)
  | k + 1, .N2 _ v => .N2 b2 (simPropView b1 b2 k v)
  | k + 1, .C1 _ u _ v => .C1 b1 (simPropView b1 b2 k u) b2 (simPropView b1 b2 k v)
  | k + 1, .C2 _ v _ u => .C2 b2 (simPropView b1 b2 k v) b1 (simPropView b1 b2 k u)

def propSignals (b1 b2 : Bool) (gs : List CommGraph) : List (Signal Bool Bool) :=
  gs.map (fun g => (b1, b2, g))

lemma simPropView_eq_propSignals {X1 X2 : Type} (b1 b2 : Bool)
    (a u : List (Signal X1 X2)) :
    simPropView b1 b2 u.length (view1 (a ++ u)) = view1 (propSignals b1 b2 (graphOfHist u)) ∧
    simPropView b1 b2 u.length (view2 (a ++ u)) = view2 (propSignals b1 b2 (graphOfHist u)) := by
  induction u using List.reverseRecOn with
  | nil =>
    simpa [simPropView, propSignals, graphOfHist, view1, view2, views] using
      ownerInit_viewOf (View.I1 : View Bool Bool) View.I2 a
  | append_singleton w s ih =>
    rcases s with ⟨x1, x2, g⟩
    have hp_eq : propSignals b1 b2 (graphOfHist (w ++ [(x1, x2, g)])) =
        propSignals b1 b2 (graphOfHist w) ++ [(b1, b2, g)] := by
      simp [propSignals, graphOfHist]
    rw [List.length_append, List.length_singleton, ← List.append_assoc, hp_eq,
      view1_append_singleton, view2_append_singleton,
      view1_append_singleton, view2_append_singleton]
    cases g <;> simp [viewStep, simPropView, ih.1, ih.2]

lemma propSignals_blind1 {X1 X2 : Type} (b1 b2 b2' : Bool) (a u : List (Signal X1 X2))
    (hblind : u.length ≤ silentAge (view1 (a ++ u))) :
    view1 (propSignals b1 b2 (graphOfHist u)) = view1 (propSignals b1 b2' (graphOfHist u)) := by
  induction u using List.reverseRecOn with
  | nil => rfl
  | append_singleton w s ih =>
    rcases s with ⟨x1, x2, g⟩
    rw [List.length_append, List.length_singleton, ← List.append_assoc, view1_append_singleton] at hblind
    cases g with
    | oneToTwo =>
      simp only [viewStep, silentAge] at hblind
      have hp1 : propSignals b1 b2 (graphOfHist (w ++ [(x1, x2, .oneToTwo)])) =
          propSignals b1 b2 (graphOfHist w) ++ [(b1, b2, .oneToTwo)] := by simp [propSignals, graphOfHist]
      have hp2 : propSignals b1 b2' (graphOfHist (w ++ [(x1, x2, .oneToTwo)])) =
          propSignals b1 b2' (graphOfHist w) ++ [(b1, b2', .oneToTwo)] := by simp [propSignals, graphOfHist]
      rw [hp1, hp2, view1_append_singleton, view1_append_singleton]
      exact congrArg (View.N1 b1) (ih (by omega))
    | both => simp [viewStep, silentAge] at hblind
    | twoToOne => simp [viewStep, silentAge] at hblind

lemma propSignals_blind2 {X1 X2 : Type} (b1 b1' b2 : Bool) (a u : List (Signal X1 X2))
    (hblind : u.length ≤ silentAge (view2 (a ++ u))) :
    view2 (propSignals b1 b2 (graphOfHist u)) = view2 (propSignals b1' b2 (graphOfHist u)) := by
  induction u using List.reverseRecOn with
  | nil => rfl
  | append_singleton w s ih =>
    rcases s with ⟨x1, x2, g⟩
    rw [List.length_append, List.length_singleton, ← List.append_assoc, view2_append_singleton] at hblind
    cases g with
    | oneToTwo => simp [viewStep, silentAge] at hblind
    | both => simp [viewStep, silentAge] at hblind
    | twoToOne =>
      simp only [viewStep, silentAge] at hblind
      have hp1 : propSignals b1 b2 (graphOfHist (w ++ [(x1, x2, .twoToOne)])) =
          propSignals b1 b2 (graphOfHist w) ++ [(b1, b2, .twoToOne)] := by simp [propSignals, graphOfHist]
      have hp2 : propSignals b1' b2 (graphOfHist (w ++ [(x1, x2, .twoToOne)])) =
          propSignals b1' b2 (graphOfHist w) ++ [(b1', b2, .twoToOne)] := by simp [propSignals, graphOfHist]
      rw [hp1, hp2, view2_append_singleton, view2_append_singleton]
      exact congrArg (View.N2 b2) (ih (by omega))

lemma mem_pref_prefix {α : Type} {A : Set (ℕ → α)} {u v : List α} (h : u ++ v ∈ Pref A) :
    u ∈ Pref A ∧ v ∈ Pref (leftQuot u A) := by
  rcases h with ⟨w, hw, hpre⟩
  have hpre_u : pre w u.length = u := by
    apply List.ext_getElem
    · simp [pre]
    · intro i hi1 hi2
      have hlt : i < (u ++ v).length := by simp; omega
      have hget := congrArg (fun l => l[i]?) hpre
      have hlen_p : i < (pre w (u ++ v).length).length := by rw [hpre]; exact hlt
      rw [List.getElem?_eq_getElem hlen_p, List.getElem?_eq_getElem hlt,
        List.getElem_append_left hi2] at hget
      simpa [pre] using Option.some.inj hget
  refine ⟨⟨w, hw, hpre_u⟩, ?_⟩
  let w_tail : ℕ → α := fun n => w (u.length + n)
  have happ : append u w_tail = w := by
    funext n
    unfold append
    split_ifs with hn
    · have hget := congrArg (fun l => l[n]?) hpre_u
      have hlen_p : n < (pre w u.length).length := by rw [hpre_u]; exact hn
      rw [List.getElem?_eq_getElem hlen_p, List.getElem?_eq_getElem hn] at hget
      simpa [pre] using (Option.some.inj hget).symm
    · dsimp only [w_tail]; congr 1; omega
  refine ⟨w_tail, by change append u w_tail ∈ A; rwa [happ], ?_⟩
  apply List.ext_getElem
  · simp [pre]
  · intro i hi1 hi2
    have hlt : u.length + i < (u ++ v).length := by simp [hi2]
    have hget := congrArg (fun l => l[u.length + i]?) hpre
    have hlen_p : u.length + i < (pre w (u ++ v).length).length := by rw [hpre]; exact hlt
    rw [List.getElem?_eq_getElem hlen_p, List.getElem?_eq_getElem hlt,
      List.getElem_append_right (Nat.le_add_right u.length i)] at hget
    simpa [pre, w_tail] using Option.some.inj hget

lemma consensus_decides_at_D {D : ℕ} (hD : 1 ≤ D)
    {B_adv : Set (ℕ → CommGraph)} {f : Algorithm Bool Bool (Option Bool) (Option Bool)}
    (hSolves : Solves (consensus Bool) f B_adv) (hDec : DecidesWithin f B_adv D)
    (b1 b2 : Bool) {gs : List CommGraph} (hlen : gs.length = D) (hlive : gs ∈ Pref B_adv) :
    ∃ o : Bool, (o = b1 ∨ o = b2) ∧
      f.f1 (view1 (propSignals b1 b2 gs)) = some o ∧
      f.f2 (view2 (propSignals b1 b2 gs)) = some o := by
  rcases hlive with ⟨w_g, hw_in, hw_pre⟩
  let h_sig : ℕ → Signal Bool Bool := fun n => (b1, b2, w_g n)
  have hgraph : graphOf h_sig ∈ B_adv := hw_in
  have hpre_sig : pre h_sig D = propSignals b1 b2 gs := by
    rw [← hlen, ← hw_pre]
    apply List.ext_getElem
    · simp [pre, propSignals]
    · intro i hi1 hi2; simp [pre, propSignals, h_sig]
  have hpersist1 : ∀ {r : ℕ} (hr : 1 ≤ r) {o : Bool}, outAt1 f h_sig r = some o →
      ∀ k : ℕ, outAt1 f h_sig (r + k) = some o := by
    intro r hr o ho k
    induction k with
    | zero => simpa using ho
    | succ k ih => exact (hSolves.1 h_sig hgraph (r + k) (by omega)).1 o ih
  have hpersist2 : ∀ {r : ℕ} (hr : 1 ≤ r) {o : Bool}, outAt2 f h_sig r = some o →
      ∀ k : ℕ, outAt2 f h_sig (r + k) = some o := by
    intro r hr o ho k
    induction k with
    | zero => simpa using ho
    | succ k ih => exact (hSolves.1 h_sig hgraph (r + k) (by omega)).2 o ih
  have hne1 : outAt1 f h_sig D ≠ none := fun hn => Nat.lt_irrefl D ((hDec h_sig hgraph D hD).1 hn)
  have hne2 : outAt2 f h_sig D ≠ none := fun hn => Nat.lt_irrefl D ((hDec h_sig hgraph D hD).2 hn)
  obtain ⟨d1, hd1⟩ := Option.ne_none_iff_exists'.mp hne1
  obtain ⟨d2, hd2⟩ := Option.ne_none_iff_exists'.mp hne2
  obtain ⟨r0, hr0, o1, o2, ho1, ho2, heq_o, hval_o⟩ := hSolves.2 h_sig hgraph
  dsimp only [consensus] at heq_o hval_o
  have hd1_eq : d1 = o1 := by
    have hA := hpersist1 hD hd1 r0
    have hB := hpersist1 hr0 ho1 D
    rw [Nat.add_comm] at hB
    exact Option.some.inj (hA.symm.trans hB)
  have hd2_eq : d2 = o2 := by
    have hA := hpersist2 hD hd2 r0
    have hB := hpersist2 hr0 ho2 D
    rw [Nat.add_comm] at hB
    exact Option.some.inj (hA.symm.trans hB)
  have hout1 : outAt1 f h_sig D = f.f1 (view1 (propSignals b1 b2 gs)) := by
    simp [outAt1, hpre_sig]
  have hout2 : outAt2 f h_sig D = f.f2 (view2 (propSignals b1 b2 gs)) := by
    simp [outAt2, hpre_sig]
  refine ⟨o1, by simpa [h_sig] using hval_o, ?_, ?_⟩
  · rw [← hout1, hd1, hd1_eq]
  · rw [← hout2, hd2, hd2_eq, ← heq_o]

lemma broadcaster_common_view {X1 X2 : Type} {A : Set (ℕ → CommGraph)} {D : ℕ} (hD : 1 ≤ D)
    (hCons : ∀ g ∈ Pref A, ConsensusSolvableWithin Bool (leftQuot g A) D)
    (r : ℕ) {C : Finset (List (Signal X1 X2))} (hne : C.Nonempty)
    (hlen : ∀ h ∈ C, h.length = r + D)
    (hlive : ∀ h ∈ C, graphOfHist h ∈ Pref A)
    (hconn : ∀ h1 ∈ C, ∀ h2 ∈ C,
      Relation.ReflTransGen (fun x y => x ∈ C ∧ y ∈ C ∧ EdgeAdj x y) h1 h2) :
    ∃ p : Proc, ∀ h1 ∈ C, ∀ h2 ∈ C, viewOf p (h1.take r) = viewOf p (h2.take r) := by
  classical
  let alg (g : List CommGraph) : Algorithm Bool Bool (Option Bool) (Option Bool) :=
    if hg : g ∈ Pref A then (hCons g hg).choose else ⟨fun _ => none, fun _ => none⟩
  have halg_spec : ∀ {g : List CommGraph} (hg : g ∈ Pref A),
      Solves (consensus Bool) (alg g) (leftQuot g A) ∧ DecidesWithin (alg g) (leftQuot g A) D := by
    intro g hg; simp only [alg, dif_pos hg]; exact (hCons g hg).choose_spec
  have hsplit_live : ∀ {h : List (Signal X1 X2)}, h ∈ C →
      graphOfHist (h.take r) ∈ Pref A ∧
      graphOfHist (h.drop r) ∈ Pref (leftQuot (graphOfHist (h.take r)) A) ∧
      (h.take r).length = r ∧ (h.drop r).length = D := by
    intro h hh
    have hl := hlen h hh
    have hcat : graphOfHist (h.take r) ++ graphOfHist (h.drop r) ∈ Pref A := by
      unfold graphOfHist
      rw [← List.map_append, List.take_append_drop]
      exact hlive h hh
    exact ⟨(mem_pref_prefix hcat).1, (mem_pref_prefix hcat).2,
      by simp [hl], by simp [hl]⟩
  have hdec : ∀ (e : C), ∃ o : Bool,
      (alg (graphOfHist (e.val.take r))).f1 (view1 (propSignals false true (graphOfHist (e.val.drop r)))) = some o ∧
      (alg (graphOfHist (e.val.take r))).f2 (view2 (propSignals false true (graphOfHist (e.val.drop r)))) = some o := by
    intro e
    obtain ⟨hg1, hg2, _, hdu⟩ := hsplit_live e.property
    obtain ⟨o, _, ho1, ho2⟩ := consensus_decides_at_D hD (halg_spec hg1).1 (halg_spec hg1).2
      false true (by simpa [graphOfHist] using hdu) hg2
    exact ⟨o, ho1, ho2⟩
  let chosenBit (e : C) : Bool := (hdec e).choose
  let chosenProc (e : C) : Proc := if chosenBit e = false then .one else .two
  have hchosen_1 : ∀ (e : C),
      (alg (graphOfHist (e.val.take r))).f1
        (view1 (propSignals false true (graphOfHist (e.val.drop r)))) = some (chosenBit e) :=
    fun e => (hdec e).choose_spec.1
  have hchosen_2 : ∀ (e : C),
      (alg (graphOfHist (e.val.take r))).f2
        (view2 (propSignals false true (graphOfHist (e.val.drop r)))) = some (chosenBit e) :=
    fun e => (hdec e).choose_spec.2
  have hblind_proc : ∀ (e : C) (p : Proc),
      D ≤ silentAge (viewOf p e.val) → chosenProc e = p := by
    intro e p hbl
    obtain ⟨hg1, hg2, _, hdu⟩ := hsplit_live e.property
    have hcat : e.val.take r ++ e.val.drop r = e.val := List.take_append_drop r e.val
    cases p with
    | one =>
      obtain ⟨o0, ho0_val, ho0_1, _⟩ := consensus_decides_at_D hD (halg_spec hg1).1 (halg_spec hg1).2
        false false (by simpa [graphOfHist] using hdu) hg2
      have ho0_false : o0 = false := ho0_val.elim id id
      have hbl' : (e.val.drop r).length ≤ silentAge (view1 (e.val.take r ++ e.val.drop r)) := by
        rw [hcat, hdu]; exact hbl
      have hv_eq := propSignals_blind1 false true false (e.val.take r) (e.val.drop r) hbl'
      have hbit : chosenBit e = false := by
        have h1 := hchosen_1 e
        rw [hv_eq, ho0_1, ho0_false] at h1
        exact Option.some.inj h1.symm
      simp [chosenProc, hbit]
    | two =>
      obtain ⟨o0, ho0_val, _, ho0_2⟩ := consensus_decides_at_D hD (halg_spec hg1).1 (halg_spec hg1).2
        true true (by simpa [graphOfHist] using hdu) hg2
      have ho0_true : o0 = true := ho0_val.elim id id
      have hbl' : (e.val.drop r).length ≤ silentAge (view2 (e.val.take r ++ e.val.drop r)) := by
        rw [hcat, hdu]; exact hbl
      have hv_eq := propSignals_blind2 false true true (e.val.take r) (e.val.drop r) hbl'
      have hbit : chosenBit e = true := by
        have h2 := hchosen_2 e
        rw [hv_eq, ho0_2, ho0_true] at h2
        exact Option.some.inj h2.symm
      simp [chosenProc, hbit]
  let tag (e : C) : Proc × View X1 X2 := (chosenProc e, viewOf (chosenProc e) (e.val.take r))
  have htag_step : ∀ (e1 e2 : C), EdgeAdj e1.val e2.val → tag e1 = tag e2 := by
    intro e1 e2 hadj
    obtain ⟨_, _, hta1, hdu1⟩ := hsplit_live e1.property
    obtain ⟨_, _, hta2, hdu2⟩ := hsplit_live e2.property
    have hcat1 : e1.val.take r ++ e1.val.drop r = e1.val := List.take_append_drop r e1.val
    have hcat2 : e2.val.take r ++ e2.val.drop r = e2.val := List.take_append_drop r e2.val
    have step_for (p : Proc) (hsame : viewOf p e1.val = viewOf p e2.val) : tag e1 = tag e2 := by
      by_cases hrec : silentAge (viewOf p e1.val) < D
      · have hsame' : viewOf p (e1.val.take r ++ e1.val.drop r) =
            viewOf p (e2.val.take r ++ e2.val.drop r) := by rwa [hcat1, hcat2]
        have hroots : e1.val.take r = e2.val.take r :=
          recent_comm_prefix_eq (hta1.trans hta2.symm) (hdu1.trans hdu2.symm) hsame'
            (by rwa [hcat1, hdu1])
        have hbit_eq : chosenBit e1 = chosenBit e2 := by
          cases p with
          | one =>
            have hsim : view1 (propSignals false true (graphOfHist (e1.val.drop r))) =
                view1 (propSignals false true (graphOfHist (e2.val.drop r))) := by
              rw [← (simPropView_eq_propSignals false true (e1.val.take r) (e1.val.drop r)).1,
                ← (simPropView_eq_propSignals false true (e2.val.take r) (e2.val.drop r)).1,
                hdu1, hdu2, hcat1, hcat2]
              exact congrArg (simPropView false true D) hsame
            have h1 := hchosen_1 e1
            have h2 := hchosen_1 e2
            rw [hroots, hsim, h2] at h1
            exact Option.some.inj h1.symm
          | two =>
            have hsim : view2 (propSignals false true (graphOfHist (e1.val.drop r))) =
                view2 (propSignals false true (graphOfHist (e2.val.drop r))) := by
              rw [← (simPropView_eq_propSignals false true (e1.val.take r) (e1.val.drop r)).2,
                ← (simPropView_eq_propSignals false true (e2.val.take r) (e2.val.drop r)).2,
                hdu1, hdu2, hcat1, hcat2]
              exact congrArg (simPropView false true D) hsame
            have h1 := hchosen_2 e1
            have h2 := hchosen_2 e2
            rw [hroots, hsim, h2] at h1
            exact Option.some.inj h1.symm
        have hp_eq : chosenProc e1 = chosenProc e2 := by simp [chosenProc, hbit_eq]
        simp [tag, hp_eq, hroots]
      · have hbl1 : D ≤ silentAge (viewOf p e1.val) := by omega
        have hbl2 : D ≤ silentAge (viewOf p e2.val) := by rwa [← hsame]
        have hp1 := hblind_proc e1 p hbl1
        have hp2 := hblind_proc e2 p hbl2
        have hsame' : viewOf p (e1.val.take r ++ e1.val.drop r) =
            viewOf p (e2.val.take r ++ e2.val.drop r) := by rwa [hcat1, hcat2]
        have hv_pre := (viewOf_prefix_eq (hta1.trans hta2.symm) hsame').2
        simp [tag, hp1, hp2, hv_pre]
    rcases hadj with hv1 | hv2
    · exact step_for .one hv1
    · exact step_for .two hv2
  obtain ⟨anchor, hanchor⟩ := hne
  refine ⟨chosenProc ⟨anchor, hanchor⟩, ?_⟩
  have htag_const : ∀ (h : List (Signal X1 X2)) (hh : h ∈ C),
      tag ⟨anchor, hanchor⟩ = tag ⟨h, hh⟩ := by
    intro h hh
    have hpath := hconn anchor hanchor h hh
    induction hpath with
    | refl => rfl
    | @tail b c _ hedge ih =>
      exact (ih hedge.1).trans (htag_step ⟨b, hedge.1⟩ ⟨c, hedge.2.1⟩ hedge.2.2)
  intro h1 hh1 h2 hh2
  have ht1 := htag_const h1 hh1
  have ht2 := htag_const h2 hh2
  have hp1 : chosenProc ⟨anchor, hanchor⟩ = chosenProc ⟨h1, hh1⟩ := congrArg Prod.fst ht1
  have hp2 : chosenProc ⟨anchor, hanchor⟩ = chosenProc ⟨h2, hh2⟩ := congrArg Prod.fst ht2
  have hv1 : viewOf (chosenProc ⟨anchor, hanchor⟩) (anchor.take r) =
      viewOf (chosenProc ⟨h1, hh1⟩) (h1.take r) := congrArg Prod.snd ht1
  have hv2 : viewOf (chosenProc ⟨anchor, hanchor⟩) (anchor.take r) =
      viewOf (chosenProc ⟨h2, hh2⟩) (h2.take r) := congrArg Prod.snd ht2
  rw [← hp1] at hv1
  rw [← hp2] at hv2
  exact hv1.symm.trans hv2

noncomputable def endTableOf {X1 X2 QB : Type} [DecidableEq X1] [DecidableEq X2]
    (D : ℕ) (C : Finset (List (Signal X1 X2))) (st : List (Signal X1 X2) → QB)
    (a : List (Signal X1 X2)) : (Fin D → Signal X1 X2) → Option QB :=
  fun u => if a ++ List.ofFn u ∈ C then some (st (a ++ List.ofFn u)) else none

lemma endpoint_table_folding {X1 X2 QB : Type} [Fintype X1] [Fintype X2]
    [DecidableEq X1] [DecidableEq X2] [Fintype QB]
    {A : Set (ℕ → CommGraph)} {D : ℕ} (hD : 1 ≤ D)
    (hCons : ∀ g ∈ Pref A, ConsensusSolvableWithin Bool (leftQuot g A) D)
    (r : ℕ) {C : Finset (List (Signal X1 X2))} (hne : C.Nonempty)
    (hlen : ∀ h ∈ C, h.length = r + D)
    (hlive : ∀ h ∈ C, graphOfHist h ∈ Pref A)
    (hconn : ∀ h1 ∈ C, ∀ h2 ∈ C,
      Relation.ReflTransGen (fun x y => x ∈ C ∧ y ∈ C ∧ EdgeAdj x y) h1 h2)
    (st : List (Signal X1 X2) → QB)
    (rep : List (Signal X1 X2) → List (Signal X1 X2))
    (hrep_mem : ∀ a ∈ C.image (List.take r), rep a ∈ C.image (List.take r))
    (hrep_pres : ∀ a ∈ C.image (List.take r), endTableOf D C st (rep a) = endTableOf D C st a)
    (hrep_const : ∀ a1 ∈ C.image (List.take r), ∀ a2 ∈ C.image (List.take r),
      endTableOf D C st a1 = endTableOf D C st a2 → rep a1 = rep a2) :
    let foldEdge := fun h : List (Signal X1 X2) => rep (h.take r) ++ h.drop r
    (∀ h ∈ C, foldEdge h ∈ C) ∧
    (∀ h ∈ C, foldEdge (foldEdge h) = foldEdge h) ∧
    (∀ h ∈ C, st (foldEdge h) = st h) ∧
    (∀ h1 ∈ C, ∀ h2 ∈ C, ∀ p : Proc,
      viewOf p h1 = viewOf p h2 → viewOf p (foldEdge h1) = viewOf p (foldEdge h2)) ∧
    (C.image foldEdge).card ≤
      (1 + Fintype.card QB) ^ (Fintype.card (Signal X1 X2) ^ D) *
        (Fintype.card (Signal X1 X2) ^ D) := by
  classical
  intro foldEdge
  have htake_gen : ∀ (u v : List (Signal X1 X2)), u.length = r → (u ++ v).take r = u :=
    fun u v hr => hr ▸ List.take_left
  have hdrop_gen : ∀ (u v : List (Signal X1 X2)), u.length = r → (u ++ v).drop r = v :=
    fun u v hr => hr ▸ List.drop_left
  have hroot_len : ∀ a ∈ C.image (List.take r), a.length = r := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨h, hh, rfl⟩
    have hl := hlen h hh
    rw [List.length_take, hl]; omega
  have hdrop_ofFn : ∀ {h : List (Signal X1 X2)}, h ∈ C →
      ∃ u : Fin D → Signal X1 X2, h.drop r = List.ofFn u := by
    intro h hh
    have hl := hlen h hh
    have hd : (h.drop r).length = D := by rw [List.length_drop, hl]; omega
    refine ⟨fun i => (h.drop r)[i.val]'(by omega), ?_⟩
    apply List.ext_getElem
    · simp [hd]
    · intro i hi1 hi2; simp
  have hentry : ∀ {h : List (Signal X1 X2)} (hh : h ∈ C),
      foldEdge h ∈ C ∧ st (foldEdge h) = st h := by
    intro h hh
    have ha_mem : h.take r ∈ C.image (List.take r) := Finset.mem_image_of_mem _ hh
    obtain ⟨u, hu⟩ := hdrop_ofFn hh
    have hcat : h.take r ++ List.ofFn u = h := by rw [← hu, List.take_append_drop]
    have hpres := congrFun (hrep_pres (h.take r) ha_mem) u
    simp only [endTableOf, hcat, if_pos hh] at hpres
    have hfold_eq : foldEdge h = rep (h.take r) ++ List.ofFn u := by dsimp [foldEdge]; rw [hu]
    rw [hfold_eq]
    split_ifs at hpres with hmem'
    · exact ⟨hmem', Option.some.inj hpres⟩
  have hidem : ∀ h ∈ C, foldEdge (foldEdge h) = foldEdge h := by
    intro h hh
    have ha_mem : h.take r ∈ C.image (List.take r) := Finset.mem_image_of_mem _ hh
    have hra_mem : rep (h.take r) ∈ C.image (List.take r) := hrep_mem _ ha_mem
    have hlen_ra : (rep (h.take r)).length = r := hroot_len _ hra_mem
    have htake_fold : (foldEdge h).take r = rep (h.take r) := htake_gen _ _ hlen_ra
    have hdrop_fold : (foldEdge h).drop r = h.drop r := hdrop_gen _ _ hlen_ra
    have hrep_idem : rep (rep (h.take r)) = rep (h.take r) :=
      hrep_const _ hra_mem _ ha_mem (hrep_pres _ ha_mem)
    dsimp only [foldEdge]
    rw [htake_fold, hdrop_fold, hrep_idem]
  obtain ⟨p_star, hcommon⟩ := broadcaster_common_view hD hCons r hne hlen hlive hconn
  have hcommon_roots : ∀ a1 ∈ C.image (List.take r), ∀ a2 ∈ C.image (List.take r),
      viewOf p_star a1 = viewOf p_star a2 := by
    intro a1 ha1 a2 ha2
    rcases Finset.mem_image.mp ha1 with ⟨h1, hh1, rfl⟩
    rcases Finset.mem_image.mp ha2 with ⟨h2, hh2, rfl⟩
    exact hcommon h1 hh1 h2 hh2
  have hviews : ∀ h1 ∈ C, ∀ h2 ∈ C, ∀ p : Proc,
      viewOf p h1 = viewOf p h2 → viewOf p (foldEdge h1) = viewOf p (foldEdge h2) := by
    intro h1 hh1 h2 hh2 p hsame
    have ha1 : h1.take r ∈ C.image (List.take r) := Finset.mem_image_of_mem _ hh1
    have ha2 : h2.take r ∈ C.image (List.take r) := Finset.mem_image_of_mem _ hh2
    have hbase : ∀ q : Proc, viewOf q (h1.take r) = viewOf q (h2.take r) →
        viewOf q (rep (h1.take r)) = viewOf q (rep (h2.take r)) := by
      intro q hq
      by_cases hqp : q = p_star
      · subst hqp
        exact hcommon_roots _ (hrep_mem _ ha1) _ (hrep_mem _ ha2)
      · have hv_star : viewOf p_star (h1.take r) = viewOf p_star (h2.take r) :=
          hcommon_roots _ ha1 _ ha2
        have ha_eq : h1.take r = h2.take r := by
          cases q <;> cases p_star
          · exact False.elim (hqp rfl)
          · exact views_injective hq hv_star
          · exact views_injective hv_star hq
          · exact False.elim (hqp rfl)
        rw [ha_eq]
    have hcat1 : h1.take r ++ h1.drop r = h1 := List.take_append_drop r h1
    have hcat2 : h2.take r ++ h2.drop r = h2 := List.take_append_drop r h2
    have hdu : (h1.drop r).length = (h2.drop r).length := by
      rw [List.length_drop, List.length_drop, hlen h1 hh1, hlen h2 hh2]
    exact view_extension hbase hdu p (by rwa [hcat1, hcat2])
  refine ⟨fun h hh => (hentry hh).1, hidem, fun h hh => (hentry hh).2, hviews, ?_⟩
  let img := C.image foldEdge
  have himg_memC : ∀ (x : img), x.val ∈ C := by
    intro x
    rcases Finset.mem_image.mp x.property with ⟨h, hh, hfx⟩
    exact hfx ▸ (hentry hh).1
  have himg_drop : ∀ (x : img), (x.val.drop r).length = D := by
    intro x
    rw [List.length_drop, hlen x.val (himg_memC x)]
    omega
  let code : img → ((Fin D → Signal X1 X2) → Option QB) × (Fin D → Signal X1 X2) :=
    fun x =>
      (endTableOf D C st (x.val.take r),
        fun i => (x.val.drop r)[i.val]'(by rw [himg_drop x]; exact i.isLt))
  have hcode_inj : Function.Injective code := by
    intro x y hxy
    rcases Finset.mem_image.mp x.property with ⟨hx0, hhx0, hfx⟩
    rcases Finset.mem_image.mp y.property with ⟨hy0, hhy0, hfy⟩
    have hxC : x.val ∈ C := himg_memC x
    have hyC : y.val ∈ C := himg_memC y
    have hx_fix : foldEdge x.val = x.val := hfx ▸ hidem hx0 hhx0
    have hy_fix : foldEdge y.val = y.val := hfy ▸ hidem hy0 hhy0
    have hrx : rep (x.val.take r) = x.val.take r := by
      have hlen_r := hroot_len _ (hrep_mem _ (Finset.mem_image_of_mem _ hxC))
      have h1 := congrArg (List.take r) hx_fix
      exact (htake_gen _ _ hlen_r).symm.trans h1
    have hry : rep (y.val.take r) = y.val.take r := by
      have hlen_r := hroot_len _ (hrep_mem _ (Finset.mem_image_of_mem _ hyC))
      have h1 := congrArg (List.take r) hy_fix
      exact (htake_gen _ _ hlen_r).symm.trans h1
    have htab_eq : endTableOf D C st (x.val.take r) = endTableOf D C st (y.val.take r) :=
      congrArg Prod.fst hxy
    have htake_eq : x.val.take r = y.val.take r :=
      hrx.symm.trans ((hrep_const _ (Finset.mem_image_of_mem _ hxC) _
        (Finset.mem_image_of_mem _ hyC) htab_eq).trans hry)
    have hdrop_eq : x.val.drop r = y.val.drop r := by
      have hsnd := congrArg Prod.snd hxy
      apply List.ext_getElem ((himg_drop x).trans (himg_drop y).symm)
      intro i hi1 hi2
      have hiD : i < D := (himg_drop x) ▸ hi1
      exact congrFun hsnd ⟨i, hiD⟩
    apply Subtype.ext
    rw [← List.take_append_drop r x.val, ← List.take_append_drop r y.val, htake_eq, hdrop_eq]
  have hcard_le := Fintype.card_le_of_injective code hcode_inj
  simp only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fun, Fintype.card_option,
    Fintype.card_fin] at hcard_le
  simpa [Nat.add_comm] using hcard_le

lemma bounded_seq_min_inf_often (K : ℕ) (c : ℕ → ℕ) (hb : ∀ n, c n ≤ K) :
    ∃ p ≤ K, (∃ᶠ n in Filter.atTop, c n = p) ∧ (∀ᶠ n in Filter.atTop, p ≤ c n) := by
  classical
  have hex : ∃ p : ℕ, p ≤ K ∧ ∃ᶠ n in Filter.atTop, c n = p := by
    by_contra hall
    have hnone : ∀ p ≤ K, ∃ N : ℕ, ∀ n ≥ N, c n ≠ p := by
      intro p hp
      have hnf : ¬ ∃ᶠ n in Filter.atTop, c n = p := fun hf => hall ⟨p, hp, hf⟩
      rw [Filter.frequently_atTop] at hnf
      by_contra hnoN
      apply hnf
      intro N
      by_contra hno_n
      exact hnoN ⟨N, fun n hn hc => hno_n ⟨n, hn, hc⟩⟩
    let boundOf : ℕ → ℕ := fun p => if hp : p ≤ K then (hnone p hp).choose else 0
    let M := (Finset.range (K + 1)).sup boundOf
    have hcM : c M ≤ K := hb M
    have hleM : boundOf (c M) ≤ M :=
      Finset.le_sup (f := boundOf) (Finset.mem_range.mpr (by omega))
    have hspec : ∀ n ≥ boundOf (c M), c n ≠ c M := by
      dsimp only [boundOf]; rw [dif_pos hcM]; exact (hnone (c M) hcM).choose_spec
    exact hspec M hleM rfl
  let p := Nat.find hex
  have hp_spec : p ≤ K ∧ ∃ᶠ n in Filter.atTop, c n = p := Nat.find_spec hex
  have hp_min : ∀ q < p, ¬ (q ≤ K ∧ ∃ᶠ n in Filter.atTop, c n = q) :=
    fun q hq => Nat.find_min hex hq
  have hno_lt : ∀ q < p, ∃ N : ℕ, ∀ n ≥ N, c n ≠ q := by
    intro q hq
    have hqK : q ≤ K := le_trans (le_of_lt hq) hp_spec.1
    have hnf : ¬ ∃ᶠ n in Filter.atTop, c n = q := fun hf => hp_min q hq ⟨hqK, hf⟩
    rw [Filter.frequently_atTop] at hnf
    by_contra hnoN
    apply hnf
    intro N
    by_contra hno_n
    exact hnoN ⟨N, fun n hn hc => hno_n ⟨n, hn, hc⟩⟩
  let boundLt : ℕ → ℕ := fun q => if hq : q < p then (hno_lt q hq).choose else 0
  let N0 := (Finset.range p).sup boundLt
  refine ⟨p, hp_spec.1, hp_spec.2, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨N0, fun n hn => ?_⟩
  by_contra hlt
  have hcp : c n < p := by omega
  have hleN : boundLt (c n) ≤ N0 := Finset.le_sup (f := boundLt) (Finset.mem_range.mpr hcp)
  have hspec : ∀ m ≥ boundLt (c n), c m ≠ c n := by
    dsimp only [boundLt]; rw [dif_pos hcp]; exact (hno_lt (c n) hcp).choose_spec
  exact hspec n (le_trans hleN hn) rfl

lemma parity_of_progress {K : ℕ} {color : ℕ → ℕ} (hbound : ∀ n, color n ≤ K)
    (Rank : ℕ → Type _) [∀ p, LinearOrder (Rank p)] [∀ p, WellFoundedLT (Rank p)]
    (rk : (p : ℕ) → ℕ → Rank p)
    (hweak : ∀ p ≤ K, ¬ Even p → ∀ n, p ≤ color n → rk p (n + 1) ≤ rk p n)
    (hstrict : ∀ p ≤ K, ¬ Even p → ∀ n, color n = p → rk p (n + 1) < rk p n) :
    ParityCond color := by
  obtain ⟨p, hp_le, hfreq, hev⟩ := bounded_seq_min_inf_often K color hbound
  by_cases heven : Even p
  · exact ⟨p, heven, hfreq, hev⟩
  · rcases Filter.eventually_atTop.mp hev with ⟨N, hN⟩
    have hanti : Antitone (fun k => rk p (N + k)) := by
      apply antitone_nat_of_succ_le
      intro k
      exact hweak p hp_le heven (N + k) (hN (N + k) (by omega))
    obtain ⟨least, ⟨k0, hk0⟩, hmin⟩ :=
      (wellFounded_lt : WellFounded ((· < ·) : Rank p → Rank p → Prop)).has_min
        (Set.range (fun k => rk p (N + k))) ⟨rk p N, 0, by simp⟩
    rcases (Filter.frequently_atTop.mp hfreq) (N + k0) with ⟨m, hm_ge, hm_eq⟩
    have hle_m : rk p m ≤ rk p (N + k0) := by
      have h := hanti (show k0 ≤ m - N by omega)
      simpa [Nat.add_sub_of_le (show N ≤ m by omega)] using h
    have hlt_m : rk p (m + 1) < rk p m := hstrict p hp_le heven m hm_eq
    have hmem : rk p (m + 1) ∈ Set.range (fun k => rk p (N + k)) :=
      ⟨m + 1 - N, by simp [Nat.add_sub_of_le (show N ≤ m + 1 by omega)]⟩
    exfalso
    apply hmin (rk p (m + 1)) hmem
    rw [← hk0]
    exact lt_of_lt_of_le hlt_m hle_m

lemma pi_lex_restrict_le {α : Type _} [LinearOrder α] {n m : ℕ} (hbound : n ≤ m)
    (a b : Fin m → α) (hle : toLex a ≤ toLex b) :
    toLex (fun i : Fin n => a ⟨i.val, lt_of_lt_of_le i.isLt hbound⟩) ≤
      toLex (fun i : Fin n => b ⟨i.val, lt_of_lt_of_le i.isLt hbound⟩) := by
  rcases lt_or_eq_of_le hle with ⟨i, hbefore, hless⟩ | heq
  · by_cases hi : i.val < n
    · exact le_of_lt ⟨⟨i.val, hi⟩,
        fun j hj => hbefore ⟨j.val, lt_of_lt_of_le j.isLt hbound⟩ hj, hless⟩
    · apply le_of_eq
      apply congrArg toLex
      funext j
      exact hbefore ⟨j.val, lt_of_lt_of_le j.isLt hbound⟩
        (show (⟨j.val, lt_of_lt_of_le j.isLt hbound⟩ : Fin m) < i from
          Nat.lt_of_lt_of_le j.isLt (Nat.not_lt.mp hi))
  · have hab : a = b := congrArg ofLex heq
    subst hab
    exact le_refl _

lemma pi_lex_le_of_pointwise {α : Type _} [LinearOrder α] {m : ℕ}
    {a b : Fin m → α} (hall : ∀ j : Fin m, a j ≤ b j) :
    toLex a ≤ toLex b :=
  not_lt.mp fun hlt => by
    rcases hlt with ⟨i, _, hi⟩
    exact not_lt_of_ge (hall i) hi

lemma pi_lex_lt_of_le_and_last_lt {α : Type _} [LinearOrder α] {p : ℕ}
    {a b : Fin (p + 1) → α} (hall : ∀ j : Fin (p + 1), a j ≤ b j)
    (hlast : a (Fin.last p) < b (Fin.last p)) :
    toLex a < toLex b := by
  refine lt_of_le_of_ne (pi_lex_le_of_pointwise hall) ?_
  intro heq
  exact (ne_of_lt hlast) (congrFun (congrArg ofLex heq) (Fin.last p))

def EdgeSegment {E : Type} (live : List E → Prop) (priority : List E → ℕ) (p : ℕ)
    (target source : List E) : Prop :=
  live target ∧ source <+: target ∧ source.length < target.length ∧
    (∀ n, source.length < n → n ≤ target.length → p ≤ priority (target.take n)) ∧
    ∃ n, source.length < n ∧ n ≤ target.length ∧ priority (target.take n) = p

lemma EdgeSegment.prepend {E : Type} {live : List E → Prop} {priority : List E → ℕ} {p : ℕ}
    {source middle target : List E}
    (pref : source <+: middle)
    (lower : ∀ n, source.length < n → n ≤ middle.length → p ≤ priority (middle.take n))
    (seg : EdgeSegment live priority p target middle) :
    EdgeSegment live priority p target source := by
  have takes : ∀ n, n ≤ middle.length → middle.take n = target.take n := by
    intro n hn
    rcases seg.2.1 with ⟨suf, rfl⟩
    exact (List.take_append_of_le_length hn).symm
  refine ⟨seg.1, pref.trans seg.2.1, lt_of_le_of_lt pref.length_le seg.2.2.1, ?_, ?_⟩
  · intro n lo hi
    by_cases hmid : n ≤ middle.length
    · rw [← takes n hmid]; exact lower n lo hmid
    · exact seg.2.2.2.1 n (by omega) hi
  · rcases seg.2.2.2.2 with ⟨n, lo, hi, eq⟩
    exact ⟨n, lt_of_le_of_lt pref.length_le lo, hi, eq⟩

lemma edgeSegment_wellFounded {E : Type} (live : List E → Prop) (priority : List E → ℕ)
    (hclosed : ∀ h k, h <+: k → live k → live h)
    (hwinning : ∀ word : ℕ → E, (∀ n, live (pre word n)) →
      ParityCond (fun n => priority (pre word n)))
    (p : ℕ) (hodd : ¬ Even p) :
    WellFounded (EdgeSegment live priority p) := by
  rw [WellFounded.wellFounded_iff_has_min]
  intro S hSne
  by_contra hno_min
  have hno : ∀ x ∈ S, ∃ y ∈ S, EdgeSegment live priority p y x := by
    intro x hx
    by_contra hx_min
    exact hno_min ⟨x, hx, fun y hy hr => hx_min ⟨y, hy, hr⟩⟩
  classical
  let stepFn (x : S) : S := ⟨(hno x.val x.property).choose, (hno x.val x.property).choose_spec.1⟩
  have hstepRel : ∀ x : S, EdgeSegment live priority p (stepFn x).val x.val :=
    fun x => (hno x.val x.property).choose_spec.2
  let x0 : S := ⟨hSne.choose, hSne.choose_spec⟩
  let chain : ℕ → S := fun n => (stepFn^[n]) x0
  let hist : ℕ → List E := fun n => (chain n).val
  have hsteps : ∀ n, EdgeSegment live priority p (hist (n + 1)) (hist n) := by
    intro n
    dsimp only [hist, chain]
    rw [Function.iterate_succ_apply']
    exact hstepRel _
  have hstrict : StrictMono (fun n => (hist n).length) :=
    strictMono_nat_of_lt_succ (fun n => (hsteps n).2.2.1)
  have hpref_le : ∀ {a b : ℕ}, a ≤ b → hist a <+: hist b := by
    intro a b hab
    induction b with
    | zero =>
      have ha : a = 0 := by omega
      subst ha; exact List.prefix_refl _
    | succ b ih =>
      rcases Nat.eq_or_lt_of_le hab with rfl | hlt
      · exact List.prefix_refl _
      · exact (ih (by omega)).trans (hsteps b).2.1
  let word : ℕ → E := fun i =>
    (hist (i + 1))[i]'(lt_of_lt_of_le (Nat.lt_succ_self i) (hstrict.id_le (i + 1)))
  have htake_eq_pre : ∀ k n, n ≤ (hist k).length → (hist k).take n = pre word n := by
    intro k n hn
    apply List.ext_getElem
    · simp [pre, hn]
    · intro i hi1 hi2
      rw [List.getElem_take]
      simp only [pre, List.getElem_ofFn, word]
      have hi_n : i < n := by simpa [pre] using hi2
      have hp1 : hist k <+: hist (max k (i + 1)) := hpref_le (le_max_left _ _)
      have hp2 : hist (i + 1) <+: hist (max k (i + 1)) := hpref_le (le_max_right _ _)
      have hi_k : i < (hist k).length := lt_of_lt_of_le hi_n hn
      have hi_i1 : i < (hist (i + 1)).length :=
        lt_of_lt_of_le (Nat.lt_succ_self i) (hstrict.id_le (i + 1))
      have hg1 : (hist k)[i] = (hist (max k (i + 1)))[i]'(lt_of_lt_of_le hi_k hp1.length_le) := by
        rcases hp1 with ⟨_, hcat⟩; simp [← hcat, List.getElem_append_left hi_k]
      have hg2 : (hist (i + 1))[i] = (hist (max k (i + 1)))[i]'(lt_of_lt_of_le hi_i1 hp2.length_le) := by
        rcases hp2 with ⟨_, hcat⟩; simp [← hcat, List.getElem_append_left hi_i1]
      exact hg1.trans hg2.symm
  have hlive_word : ∀ n, live (pre word n) := by
    intro n
    have hle1 : n + 1 ≤ (hist (n + 1)).length := hstrict.id_le (n + 1)
    have hn_le : n ≤ (hist (n + 1)).length := by omega
    rw [← htake_eq_pre (n + 1) n hn_le]
    exact hclosed _ _ (List.take_prefix _ _) (hsteps n).1
  obtain ⟨q, hq_even, hq_freq, hq_ev⟩ := hwinning word hlive_word
  have hp_freq : ∀ N, ∃ j ≥ N, priority (pre word j) = p := by
    intro N
    obtain ⟨j, hlo, hhi, heq⟩ := (hsteps N).2.2.2.2
    have hle_N : N ≤ (hist N).length := hstrict.id_le N
    refine ⟨j, by omega, ?_⟩
    rwa [← htake_eq_pre (N + 1) j hhi]
  have hp_lower : ∀ n ≥ (hist 0).length + 1, p ≤ priority (pre word n) := by
    intro n hn
    have hex_k : ∃ k, (hist k).length < n ∧ n ≤ (hist (k + 1)).length := by
      let S_gt : Set ℕ := {m | n ≤ (hist m).length}
      have hne_gt : S_gt.Nonempty := ⟨n, hstrict.id_le n⟩
      let m := Nat.find hne_gt
      have hm_ge : n ≤ (hist m).length := Nat.find_spec hne_gt
      have hm_pos : 0 < m := by
        by_contra hm0
        have hm_z : m = 0 := by omega
        rw [hm_z] at hm_ge
        omega
      have hprev : ¬ (n ≤ (hist (m - 1)).length) :=
        Nat.find_min hne_gt (Nat.sub_lt hm_pos Nat.one_pos)
      exact ⟨m - 1, Nat.lt_of_not_ge hprev, by simpa [Nat.sub_add_cancel hm_pos] using hm_ge⟩
    rcases hex_k with ⟨k, hlo, hhi⟩
    have hb := (hsteps k).2.2.2.1 n hlo hhi
    rwa [htake_eq_pre (k + 1) n hhi] at hb
  rcases Filter.eventually_atTop.mp hq_ev with ⟨N_q, hN_q⟩
  obtain ⟨j_p, hj_p_ge, hj_p_eq⟩ := hp_freq N_q
  have hqp : q ≤ p := hj_p_eq ▸ hN_q j_p hj_p_ge
  rcases (Filter.frequently_atTop.mp hq_freq) ((hist 0).length + 1) with ⟨j_q, hj_q_ge, hj_q_eq⟩
  have hpq : p ≤ q := hj_q_eq ▸ hp_lower j_q hj_q_ge
  exact hodd (Nat.le_antisymm hpq hqp ▸ hq_even)

noncomputable def edgeCoord {E : Type} (live : List E → Prop) (priority : List E → ℕ)
    (hclosed : ∀ h k, h <+: k → live k → live h)
    (hwinning : ∀ word : ℕ → E, (∀ n, live (pre word n)) →
      ParityCond (fun n => priority (pre word n)))
    (p : ℕ) (h : List E) : Ordinal.{0} := by
  classical
  exact if hodd : ¬ Even p then
    letI : IsWellFounded (List E) (EdgeSegment live priority p) :=
      ⟨edgeSegment_wellFounded live priority hclosed hwinning p hodd⟩
    IsWellFounded.rank (EdgeSegment live priority p) h
  else 0

noncomputable def edgeRank {E : Type} (live : List E → Prop) (priority : List E → ℕ)
    (hclosed : ∀ h k, h <+: k → live k → live h)
    (hwinning : ∀ word : ℕ → E, (∀ n, live (pre word n)) →
      ParityCond (fun n => priority (pre word n)))
    (k : ℕ) (h : List E) : Lex (Fin (k + 1) → Ordinal.{0}) :=
  toLex (fun j => edgeCoord live priority hclosed hwinning j.val h)

lemma edgeCoord_le {E : Type} (live : List E → Prop) (priority : List E → ℕ)
    (hclosed : ∀ h k, h <+: k → live k → live h)
    (hwinning : ∀ word : ℕ → E, (∀ n, live (pre word n)) →
      ParityCond (fun n => priority (pre word n)))
    (p : ℕ) {source target : List E} (pref : source <+: target)
    (lower : ∀ n, source.length < n → n ≤ target.length → p ≤ priority (target.take n)) :
    edgeCoord live priority hclosed hwinning p target ≤
      edgeCoord live priority hclosed hwinning p source := by
  classical
  unfold edgeCoord
  by_cases hodd : ¬ Even p
  · rw [dif_pos hodd, dif_pos hodd]
    let _ : IsWellFounded (List E) (EdgeSegment live priority p) :=
      ⟨edgeSegment_wellFounded live priority hclosed hwinning p hodd⟩
    rw [IsWellFounded.rank_eq (EdgeSegment live priority p) target]
    apply Ordinal.iSup_le
    intro y
    exact Order.succ_le_of_lt (IsWellFounded.rank_lt_of_rel (y.2.prepend pref lower))
  · rw [dif_neg hodd, dif_neg hodd]

lemma edgeCoord_lt {E : Type} (live : List E → Prop) (priority : List E → ℕ)
    (hclosed : ∀ h k, h <+: k → live k → live h)
    (hwinning : ∀ word : ℕ → E, (∀ n, live (pre word n)) →
      ParityCond (fun n => priority (pre word n)))
    (p : ℕ) (hodd : ¬ Even p) {source target : List E}
    (seg : EdgeSegment live priority p target source) :
    edgeCoord live priority hclosed hwinning p target <
      edgeCoord live priority hclosed hwinning p source := by
  unfold edgeCoord
  rw [dif_pos hodd, dif_pos hodd]
  let _ : IsWellFounded (List E) (EdgeSegment live priority p) :=
    ⟨edgeSegment_wellFounded live priority hclosed hwinning p hodd⟩
  exact IsWellFounded.rank_lt_of_rel seg

lemma edgeRank_restrict_le {E : Type} (live : List E → Prop) (priority : List E → ℕ)
    (hclosed : ∀ h k, h <+: k → live k → live h)
    (hwinning : ∀ word : ℕ → E, (∀ n, live (pre word n)) →
      ParityCond (fun n => priority (pre word n)))
    {p K : ℕ} (hpK : p ≤ K) {h1 h2 : List E}
    (hle : edgeRank live priority hclosed hwinning K h1 ≤
      edgeRank live priority hclosed hwinning K h2) :
    edgeRank live priority hclosed hwinning p h1 ≤
      edgeRank live priority hclosed hwinning p h2 :=
  pi_lex_restrict_le (Nat.succ_le_succ hpK) _ _ hle

lemma edgeRank_le {E : Type} (live : List E → Prop) (priority : List E → ℕ)
    (hclosed : ∀ h k, h <+: k → live k → live h)
    (hwinning : ∀ word : ℕ → E, (∀ n, live (pre word n)) →
      ParityCond (fun n => priority (pre word n)))
    (p : ℕ) {source target : List E} (pref : source <+: target)
    (lower : ∀ n, source.length < n → n ≤ target.length → p ≤ priority (target.take n)) :
    edgeRank live priority hclosed hwinning p target ≤
      edgeRank live priority hclosed hwinning p source := by
  apply pi_lex_le_of_pointwise
  intro j
  exact edgeCoord_le live priority hclosed hwinning j.val pref
    (fun n lo hi => le_trans (Nat.le_of_lt_succ j.isLt) (lower n lo hi))

lemma edgeRank_lt {E : Type} (live : List E → Prop) (priority : List E → ℕ)
    (hclosed : ∀ h k, h <+: k → live k → live h)
    (hwinning : ∀ word : ℕ → E, (∀ n, live (pre word n)) →
      ParityCond (fun n => priority (pre word n)))
    (p : ℕ) (hodd : ¬ Even p) {source target : List E}
    (seg : EdgeSegment live priority p target source) :
    edgeRank live priority hclosed hwinning p target <
      edgeRank live priority hclosed hwinning p source := by
  apply pi_lex_lt_of_le_and_last_lt
  · intro j
    exact edgeCoord_le live priority hclosed hwinning j.val seg.2.1
      (fun n lo hi => le_trans (Nat.le_of_lt_succ j.isLt) (seg.2.2.2.1 n lo hi))
  · simpa [Fin.val_last] using edgeCoord_lt live priority hclosed hwinning p hodd seg

lemma folded_edges_parity {E : Type} (live : List E → Prop) (priority : List E → ℕ)
    (hclosed : ∀ h k, h <+: k → live k → live h)
    (hwinning : ∀ word : ℕ → E, (∀ n, live (pre word n)) →
      ParityCond (fun n => priority (pre word n)))
    (K : ℕ) (root chosen : ℕ → List E) (letter : ℕ → E) (color : ℕ → ℕ)
    (hcolor_bound : ∀ n, color n ≤ K)
    (hreplace : ∀ n, edgeRank live priority hclosed hwinning K (chosen n) ≤
      edgeRank live priority hclosed hwinning K (root n))
    (hnext : ∀ n, root (n + 1) = chosen n ++ [letter n])
    (hlive : ∀ n, live (root (n + 1)))
    (hlabels : ∀ n, priority (root (n + 1)) = color n) :
    ParityCond color := by
  have hpref : ∀ n, chosen n <+: root (n + 1) := fun n => ⟨[letter n], (hnext n).symm⟩
  have hgrows : ∀ n, (chosen n).length < (root (n + 1)).length := fun n => by simp [hnext n]
  have honly : ∀ n t, (chosen n).length < t → t ≤ (root (n + 1)).length →
      (root (n + 1)).take t = root (n + 1) := by
    intro n t lo hi
    have hlen : (root (n + 1)).length = (chosen n).length + 1 := by simp [hnext n]
    have ht : t = (root (n + 1)).length := by omega
    rw [ht, List.take_length]
  apply parity_of_progress hcolor_bound (fun p => Lex (Fin (p + 1) → Ordinal.{0}))
    (fun p n => edgeRank live priority hclosed hwinning p (root n))
  · intro p hp_le _ n hcut
    refine le_trans (edgeRank_le live priority hclosed hwinning p (hpref n) ?_)
      (edgeRank_restrict_le live priority hclosed hwinning hp_le (hreplace n))
    intro t lo hi
    rw [honly n t lo hi, hlabels n]
    exact hcut
  · intro p hp_le hodd n heq
    refine lt_of_lt_of_le (edgeRank_lt live priority hclosed hwinning p hodd ?_)
      (edgeRank_restrict_le live priority hclosed hwinning hp_le (hreplace n))
    refine ⟨hlive n, hpref n, hgrows n, ?_, ?_⟩
    · intro t lo hi
      rw [honly n t lo hi, hlabels n, heq]
    · exact ⟨(root (n + 1)).length, hgrows n, le_refl _,
        by rw [List.take_length, hlabels n, heq]⟩

lemma lookup_eq_of_mem_unique {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {k : α} {v : β}
    (hmem : (k, v) ∈ l) (huni : ∀ v', (k, v') ∈ l → v' = v) :
    l.lookup k = some v := by
  induction l with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    simp only [List.lookup_cons]
    by_cases hkk : (k == k') = true
    · have hk_eq : k = k' := eq_of_beq hkk
      subst hk_eq
      rw [hkk]
      exact congrArg some (huni v' (List.mem_cons.mpr (Or.inl rfl)))
    · have hk_ne : k ≠ k' := fun heq => hkk (beq_iff_eq.mpr heq)
      rw [Bool.eq_false_iff.mpr hkk]
      rcases List.mem_cons.mp hmem with heq | htl
      · exact False.elim (hk_ne (Prod.mk.inj heq).1)
      · exact ih htl (fun v'' hv'' => huni v'' (List.mem_cons_of_mem _ hv''))

lemma valid_nil {L : Type} (t : LabeledTree L) : t.Valid [] :=
  fun _ hi => by simp at hi

lemma valid_append_singleton {L : Type} {t : LabeledTree L} {a : List ℕ} {c : ℕ} :
    t.Valid (a ++ [c]) ↔ t.Valid a ∧ c < t.nChildren a := by
  constructor
  · intro hv
    refine ⟨fun i hi => ?_, ?_⟩
    · have hi' : i < (a ++ [c]).length := by simp; omega
      have h := hv i hi'
      rwa [List.getElem_append_left hi, List.take_append_of_le_length (Nat.le_of_lt hi)] at h
    · have hi' : a.length < (a ++ [c]).length := by simp
      have h := hv a.length hi'
      simpa [List.take_append_of_le_length (le_refl a.length)] using h
  · rintro ⟨hva, hc⟩ i hi
    have hlen : (a ++ [c]).length = a.length + 1 := by simp
    by_cases hi_lt : i < a.length
    · rw [List.getElem_append_left hi_lt, List.take_append_of_le_length (Nat.le_of_lt hi_lt)]
      exact hva i hi_lt
    · have hieq : i = a.length := by omega
      subst hieq
      simpa [List.take_append_of_le_length (le_refl a.length)] using hc

lemma reachableInB_zero {X1 X2 Y1 Y2 QB : Type} [Inhabited X1] [Inhabited X2]
    [Inhabited Y1] [Inhabited Y2] {D : ℕ}
    (B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))) :
    ReachableInB B 0 [] B.init :=
  ⟨by simp, fun _ => ((default, default, .both), (default, default)), by simp [pre], rfl⟩

lemma reachableInB_step {X1 X2 Y1 Y2 QB : Type} {D : ℕ}
    {B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))} {n : ℕ} {h : List (Signal X1 X2)} {q : QB}
    (hr : ReachableInB B n h q) (u : Fin D → Signal X1 X2) (ys : Fin D → Y1 × Y2) :
    ReachableInB B (n + 1) (h ++ List.ofFn u) (B.step q (fun i => (u i, ys i))) := by
  rcases hr with ⟨hlen, e, hpre, hrun⟩
  let e' : ℕ → Signal X1 X2 × (Y1 × Y2) := fun t =>
    if ht : n * D ≤ t ∧ t < (n + 1) * D then
      let idx : Fin D := ⟨t - n * D, by
        have : (n + 1) * D = n * D + D := Nat.succ_mul n D
        omega⟩
      (u idx, ys idx)
    else e t
  have hrun_eq : ∀ k ≤ n, B.run (toBlocks D e') k = B.run (toBlocks D e) k := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk_lt : k < n := Nat.lt_of_succ_le hk
      have hblk : toBlocks D e' k = toBlocks D e k := by
        funext i
        unfold toBlocks
        dsimp only [e']
        have hlt_nd : k * D + i.val < n * D := by
          have h1 : k + 1 ≤ n := hk
          calc
            k * D + i.val < k * D + D := Nat.add_lt_add_left i.isLt (k * D)
            _ = (k + 1) * D := (Nat.succ_mul k D).symm
            _ ≤ n * D := Nat.mul_le_mul_right D h1
        rw [dif_neg (by omega)]
      simp only [DPA.run, ih (Nat.le_of_lt hk_lt), hblk]
  have hblk_n : toBlocks D e' n = (fun i => (u i, ys i)) := by
    funext i
    unfold toBlocks
    dsimp only [e']
    have hcond : n * D ≤ n * D + i.val ∧ n * D + i.val < (n + 1) * D := by
      refine ⟨Nat.le_add_right _ _, ?_⟩
      rw [Nat.succ_mul]
      exact Nat.add_lt_add_left i.isLt _
    rw [dif_pos hcond]
    have hsub : (⟨n * D + i.val - n * D, by rw [Nat.succ_mul] at hcond; omega⟩ : Fin D) = i := by
      ext; simp
    rw [hsub]
  refine ⟨by simp [hlen, Nat.succ_mul], e', ?_, ?_⟩
  · apply List.ext_getElem
    · simp [pre, hlen, Nat.succ_mul]
    · intro t ht1 ht2
      simp only [pre, List.getElem_ofFn]
      by_cases ht_lt : t < n * D
      · have hth : t < h.length := hlen ▸ ht_lt
        rw [List.getElem_append_left hth]
        dsimp only [e']
        rw [dif_neg (by omega)]
        have hlen_p : t < (pre (fun s => (e s).1) (n * D)).length := by simp [pre, ht_lt]
        have heq_p : (pre (fun s => (e s).1) (n * D))[t]'hlen_p = h[t]'hth := by simp [hpre]
        simpa [pre] using heq_p
      · have ht_ge : h.length ≤ t := by omega
        have ht_bound : t < (n + 1) * D := by simpa [pre] using ht1
        rw [List.getElem_append_right ht_ge]
        dsimp only [e']
        rw [dif_pos ⟨by omega, ht_bound⟩]
        simp [hlen]
  · simp only [DPA.run, hrun_eq n (le_refl n), hrun, hblk_n]

lemma reachableInB_live {X1 X2 Y1 Y2 QB : Type} {D : ℕ}
    {A : Set (ℕ → CommGraph)} {φ : Formula X1 X2 Y1 Y2}
    {B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))} {Qlive : Set QB}
    (hB : IsBlockAutomaton A φ D B Qlive)
    {n : ℕ} {h : List (Signal X1 X2)} {q : QB} (hr : ReachableInB B n h q) :
    q ∈ Qlive ↔ graphOfHist h ∈ Pref A := by
  rcases hr with ⟨hlen, e, hpre, hrun⟩
  have hgr : pre (graphOfExec e) (n * D) = graphOfHist h := by
    rw [← hpre]
    apply List.ext_getElem
    · simp [pre, graphOfHist]
    · intro i hi1 hi2; simp [pre, graphOfExec, graphOfHist]
  rw [← hrun, hB.live e n, hgr]

lemma isComponentOf_mem {X1 X2 : Type} {S C : Set (List (Signal X1 X2))}
    (hC : IsComponentOf S C) : C.Nonempty ∧ C ⊆ S := by
  rcases hC with ⟨c, hcS, rfl⟩
  refine ⟨⟨c, Relation.ReflTransGen.refl⟩, ?_⟩
  intro h hh
  cases hh with
  | refl => exact hcS
  | tail _ hedge => exact hedge.2.1

lemma isComponentOf_eq_of_adj {X1 X2 : Type} {S C1 C2 : Set (List (Signal X1 X2))}
    (hC1 : IsComponentOf S C1) (hC2 : IsComponentOf S C2)
    {h1 h2 : List (Signal X1 X2)} (hh1 : h1 ∈ C1) (hh2 : h2 ∈ C2) (hadj : EdgeAdj h1 h2) :
    C1 = C2 := by
  have hs1 : h1 ∈ S := (isComponentOf_mem hC1).2 hh1
  have hs2 : h2 ∈ S := (isComponentOf_mem hC2).2 hh2
  rcases hC1 with ⟨c1, hc1S, rfl⟩
  rcases hC2 with ⟨c2, hc2S, rfl⟩
  let R := fun a b : List (Signal X1 X2) => a ∈ S ∧ b ∈ S ∧ EdgeAdj a b
  have hsymm : ∀ {a b}, R a b → R b a := by
    rintro a b ⟨ha, hb, hv | hv⟩
    · exact ⟨hb, ha, Or.inl hv.symm⟩
    · exact ⟨hb, ha, Or.inr hv.symm⟩
  have rev : ∀ {a b}, Relation.ReflTransGen R a b → Relation.ReflTransGen R b a := by
    intro a b hr
    induction hr with
    | refl => exact .refl
    | tail _ hedge ih => exact (Relation.ReflTransGen.single (hsymm hedge)).trans ih
  have h_c1_h1 : Relation.ReflTransGen R c1 h1 := hh1
  have h_c2_h2 : Relation.ReflTransGen R c2 h2 := hh2
  have h_h2_c2 : Relation.ReflTransGen R h2 c2 := rev h_c2_h2
  have h_c1_c2 : Relation.ReflTransGen R c1 c2 :=
    (h_c1_h1.tail ⟨hs1, hs2, hadj⟩).trans h_h2_c2
  have h_c2_c1 : Relation.ReflTransGen R c2 c1 := rev h_c1_c2
  ext x
  exact ⟨fun hx => h_c2_c1.trans hx, fun hx => h_c1_c2.trans hx⟩

lemma uncomp_node_inv {X1 X2 Y1 Y2 QB : Type}
    [DecidableEq X1] [DecidableEq X2] [Inhabited X1] [Inhabited X2] [Inhabited Y1] [Inhabited Y2]
    {D : ℕ} {B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))} {Qlive : Set QB}
    {t0 : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)}
    (ht0 : IsUncompressedComponentTree B Qlive t0) (hinit_live : B.init ∈ Qlive) :
    ∀ a : List ℕ, t0.Valid a → ∀ h s, (h, s) ∈ (t0.label a).1 →
      ReachableInB B a.length h s ∧ s ∈ Qlive ∧ (t0.label a).state B.init h = s := by
  intro a
  induction a using List.reverseRecOn with
  | nil =>
    intro _ h s hmem
    have hs : s = B.init := ht0.2.1 h s hmem
    have hh_mem : h ∈ (t0.label []).edges := ⟨s, hmem⟩
    rw [ht0.1] at hh_mem
    have hh : h = [] := hh_mem
    subst hh hs
    have hlkp : (t0.label []).1.lookup [] = some B.init :=
      lookup_eq_of_mem_unique hmem (fun s' hs' => ht0.2.1 [] s' hs')
    exact ⟨reachableInB_zero B, hinit_live, by simp [NodeLabel.state, hlkp]⟩
  | append_singleton a i ih =>
    intro hv h s hmem
    obtain ⟨hva, hi_lt⟩ := valid_append_singleton.mp hv
    obtain ⟨_, hchild, _⟩ := ht0.2.2 a hva
    obtain ⟨hcomp, hstate_eq⟩ := hchild i hi_lt
    have hh_in_live : h ∈ (t0.label a).liveExt B Qlive :=
      (isComponentOf_mem hcomp).2 ⟨s, hmem⟩
    rcases hh_in_live with ⟨e, he_mem, u, rfl, hqlam_live⟩
    rcases he_mem with ⟨se, hse_mem⟩
    obtain ⟨hreach_e, _, hstate_e⟩ := ih hva e se hse_mem
    have hs_eq : s = (t0.label a).qLam B e u := hstate_eq _ s hmem e ⟨se, hse_mem⟩ u rfl
    subst hs_eq
    have hlkp : (t0.label (a ++ [i])).1.lookup (e ++ List.ofFn u) = some ((t0.label a).qLam B e u) :=
      lookup_eq_of_mem_unique hmem (fun s' hs' => hstate_eq _ s' hs' e ⟨se, hse_mem⟩ u rfl)
    have hreach_next : ReachableInB B (a ++ [i]).length (e ++ List.ofFn u) ((t0.label a).qLam B e u) := by
      have hstep := reachableInB_step hreach_e u
        (fun j => (t0.label a).out e ((List.ofFn u).take (j.val + 1)))
      simpa [NodeLabel.qLam, hstate_e] using hstep
    exact ⟨hreach_next, hqlam_live, by simp [NodeLabel.state, hlkp]⟩

lemma uncomp_nodes_eq_of_view {X1 X2 Y1 Y2 QB : Type}
    [DecidableEq X1] [DecidableEq X2] [Inhabited X1] [Inhabited X2] [Inhabited Y1] [Inhabited Y2]
    {D : ℕ} {B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))} {Qlive : Set QB}
    {t0 : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)}
    (ht0 : IsUncompressedComponentTree B Qlive t0) (hinit_live : B.init ∈ Qlive)
    {a1 a2 : List ℕ} (hv1 : t0.Valid a1) (hv2 : t0.Valid a2) (hlen : a1.length = a2.length)
    {h1 h2 : List (Signal X1 X2)} (hh1 : h1 ∈ (t0.label a1).edges) (hh2 : h2 ∈ (t0.label a2).edges)
    (hadj : EdgeAdj h1 h2) :
    a1 = a2 := by
  induction a1 using List.reverseRecOn generalizing a2 h1 h2 with
  | nil => exact (List.eq_nil_of_length_eq_zero hlen.symm).symm
  | append_singleton a1' i1 ih =>
    cases a2 using List.reverseRecOn with
    | nil => simp at hlen
    | append_singleton a2' i2 =>
      have hlen' : a1'.length = a2'.length := by simpa using hlen
      obtain ⟨hva1, hi1⟩ := valid_append_singleton.mp hv1
      obtain ⟨hva2, hi2⟩ := valid_append_singleton.mp hv2
      obtain ⟨hcomp1, _⟩ := (ht0.2.2 a1' hva1).2.1 i1 hi1
      obtain ⟨hcomp2, _⟩ := (ht0.2.2 a2' hva2).2.1 i2 hi2
      have hl1 : h1 ∈ (t0.label a1').liveExt B Qlive := (isComponentOf_mem hcomp1).2 hh1
      have hl2 : h2 ∈ (t0.label a2').liveExt B Qlive := (isComponentOf_mem hcomp2).2 hh2
      rcases hl1 with ⟨e1, he1, u1, rfl, _⟩
      rcases hl2 with ⟨e2, he2, u2, rfl, _⟩
      rcases he1 with ⟨s1, hs1⟩
      rcases he2 with ⟨s2, hs2⟩
      have hlen_e1 : e1.length = a1'.length * D := (uncomp_node_inv ht0 hinit_live a1' hva1 e1 s1 hs1).1.1
      have hlen_e2 : e2.length = a2'.length * D := (uncomp_node_inv ht0 hinit_live a2' hva2 e2 s2 hs2).1.1
      have hlen_e12 : e1.length = e2.length := hlen_e1.trans (hlen' ▸ hlen_e2.symm)
      have hadj_e : EdgeAdj e1 e2 := by
        rcases hadj with hv | hv
        · exact Or.inl (viewOf_prefix_eq (p := .one) hlen_e12 hv).2
        · exact Or.inr (viewOf_prefix_eq (p := .two) hlen_e12 hv).2
      have ha_eq : a1' = a2' := ih hva1 hva2 hlen' ⟨s1, hs1⟩ ⟨s2, hs2⟩ hadj_e
      subst ha_eq
      have hC_eq : (t0.label (a1' ++ [i1])).edges = (t0.label (a1' ++ [i2])).edges :=
        isComponentOf_eq_of_adj hcomp1 hcomp2 hh1 hh2 hadj
      obtain ⟨_, _, huniq⟩ := (ht0.2.2 a1' hva1).2.2 (t0.label (a1' ++ [i1])).edges hcomp1
      have hi1_eq := huniq i1 ⟨hi1, rfl⟩
      have hi2_eq := huniq i2 ⟨hi2, hC_eq.symm⟩
      rw [hi1_eq, ← hi2_eq]

def blockConcat {X1 X2 : Type} {D : ℕ} (ws : List (Fin D → Signal X1 X2)) : List (Signal X1 X2) :=
  ws.foldl (fun acc u => acc ++ List.ofFn u) []

@[simp] lemma blockConcat_nil {X1 X2 : Type} {D : ℕ} :
    blockConcat ([] : List (Fin D → Signal X1 X2)) = [] := rfl

lemma blockConcat_append_singleton {X1 X2 : Type} {D : ℕ}
    (ws : List (Fin D → Signal X1 X2)) (u : Fin D → Signal X1 X2) :
    blockConcat (ws ++ [u]) = blockConcat ws ++ List.ofFn u := by
  simp [blockConcat]

lemma blockConcat_length {X1 X2 : Type} {D : ℕ} (ws : List (Fin D → Signal X1 X2)) :
    (blockConcat ws).length = ws.length * D := by
  induction ws using List.reverseRecOn with
  | nil => simp
  | append_singleton ws u ih =>
    rw [blockConcat_append_singleton, List.length_append, List.length_ofFn, ih]
    simp [Nat.succ_mul]

lemma uncomp_occurrence {X1 X2 Y1 Y2 QB : Type}
    [DecidableEq X1] [DecidableEq X2] [Inhabited X1] [Inhabited X2] [Inhabited Y1] [Inhabited Y2]
    {D : ℕ} {A : Set (ℕ → CommGraph)} {φ : Formula X1 X2 Y1 Y2}
    {B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))} {Qlive : Set QB}
    (hB : IsBlockAutomaton A φ D B Qlive)
    {t0 : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)}
    (ht0 : IsUncompressedComponentTree B Qlive t0) (hlive0 : ([] : List CommGraph) ∈ Pref A)
    (ws : List (Fin D → Signal X1 X2))
    (hlive : graphOfHist (blockConcat ws) ∈ Pref A) :
    ∃! a : List ℕ, t0.Valid a ∧ a.length = ws.length ∧ blockConcat ws ∈ (t0.label a).edges := by
  have hinit_live : B.init ∈ Qlive := (reachableInB_live hB (reachableInB_zero B)).mpr hlive0
  have hex : ∃ a : List ℕ, t0.Valid a ∧ a.length = ws.length ∧ blockConcat ws ∈ (t0.label a).edges := by
    induction ws using List.reverseRecOn with
    | nil =>
      refine ⟨[], valid_nil t0, rfl, ?_⟩
      rw [ht0.1]; rfl
    | append_singleton ws u ih =>
      rw [blockConcat_append_singleton] at hlive
      have hlive_parent : graphOfHist (blockConcat ws) ∈ Pref A := by
        have hcat : graphOfHist (blockConcat ws) ++ graphOfHist (List.ofFn u) ∈ Pref A := by
          simpa [graphOfHist] using hlive
        exact (mem_pref_prefix hcat).1
      obtain ⟨a, hva, hlen_a, hmem_a⟩ := ih hlive_parent
      rcases hmem_a with ⟨sa, hsa⟩
      obtain ⟨hreach_a, _, hstate_a⟩ := uncomp_node_inv ht0 hinit_live a hva _ sa hsa
      have hreach_next : ReachableInB B (a.length + 1) (blockConcat ws ++ List.ofFn u)
          ((t0.label a).qLam B (blockConcat ws) u) := by
        have hstep := reachableInB_step hreach_a u
          (fun j => (t0.label a).out (blockConcat ws) ((List.ofFn u).take (j.val + 1)))
        simpa [NodeLabel.qLam, hstate_a] using hstep
      have hqlam_live : (t0.label a).qLam B (blockConcat ws) u ∈ Qlive :=
        (reachableInB_live hB hreach_next).mpr hlive
      let h_next := blockConcat ws ++ List.ofFn u
      let S := (t0.label a).liveExt B Qlive
      have hh_in_S : h_next ∈ S := ⟨blockConcat ws, ⟨sa, hsa⟩, u, rfl, hqlam_live⟩
      let C : Set (List (Signal X1 X2)) :=
        {x | Relation.ReflTransGen (fun x1 x2 => x1 ∈ S ∧ x2 ∈ S ∧ EdgeAdj x1 x2) h_next x}
      have hcomp_C : IsComponentOf S C := ⟨h_next, hh_in_S, rfl⟩
      obtain ⟨i, ⟨hi_lt, hC_eq⟩, _⟩ := (ht0.2.2 a hva).2.2 C hcomp_C
      refine ⟨a ++ [i], valid_append_singleton.mpr ⟨hva, hi_lt⟩, by simp [hlen_a], ?_⟩
      rw [blockConcat_append_singleton, hC_eq]
      exact Relation.ReflTransGen.refl
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, ha, fun a' ha' => ?_⟩
  exact uncomp_nodes_eq_of_view ht0 hinit_live ha'.1 ha.1
    (ha'.2.1.trans ha.2.1.symm) ha'.2.2 ha.2.2 (Or.inl rfl)

noncomputable def treeNodeOf {X1 X2 Y1 Y2 QB : Type}
    [DecidableEq X1] [DecidableEq X2] [Inhabited X1] [Inhabited X2] [Inhabited Y1] [Inhabited Y2]
    {D : ℕ} {A : Set (ℕ → CommGraph)} {φ : Formula X1 X2 Y1 Y2}
    {B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))} {Qlive : Set QB}
    (hB : IsBlockAutomaton A φ D B Qlive)
    {t0 : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)}
    (ht0 : IsUncompressedComponentTree B Qlive t0) (hlive0 : ([] : List CommGraph) ∈ Pref A)
    (ws : List (Fin D → Signal X1 X2)) : List ℕ := by
  classical
  exact if hl : graphOfHist (blockConcat ws) ∈ Pref A then
    (uncomp_occurrence hB ht0 hlive0 ws hl).choose
  else []

noncomputable def treeState {X1 X2 Y1 Y2 QB : Type}
    [DecidableEq X1] [DecidableEq X2] [Inhabited X1] [Inhabited X2] [Inhabited Y1] [Inhabited Y2]
    {D : ℕ} {A : Set (ℕ → CommGraph)} {φ : Formula X1 X2 Y1 Y2}
    {B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))} {Qlive : Set QB}
    (hB : IsBlockAutomaton A φ D B Qlive)
    {t0 : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)}
    (ht0 : IsUncompressedComponentTree B Qlive t0) (hlive0 : ([] : List CommGraph) ∈ Pref A)
    (ws : List (Fin D → Signal X1 X2)) : QB :=
  (t0.label (treeNodeOf hB ht0 hlive0 ws)).state B.init (blockConcat ws)

lemma treeNodeOf_spec {X1 X2 Y1 Y2 QB : Type}
    [DecidableEq X1] [DecidableEq X2] [Inhabited X1] [Inhabited X2] [Inhabited Y1] [Inhabited Y2]
    {D : ℕ} {A : Set (ℕ → CommGraph)} {φ : Formula X1 X2 Y1 Y2}
    {B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))} {Qlive : Set QB}
    (hB : IsBlockAutomaton A φ D B Qlive)
    {t0 : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)}
    (ht0 : IsUncompressedComponentTree B Qlive t0) (hlive0 : ([] : List CommGraph) ∈ Pref A)
    {ws : List (Fin D → Signal X1 X2)} (hl : graphOfHist (blockConcat ws) ∈ Pref A) :
    let a := treeNodeOf hB ht0 hlive0 ws
    t0.Valid a ∧ a.length = ws.length ∧ blockConcat ws ∈ (t0.label a).edges := by
  dsimp only
  unfold treeNodeOf
  rw [dif_pos hl]
  exact (uncomp_occurrence hB ht0 hlive0 ws hl).choose_spec.1

lemma treeNodeOf_append_singleton {X1 X2 Y1 Y2 QB : Type}
    [DecidableEq X1] [DecidableEq X2] [Inhabited X1] [Inhabited X2] [Inhabited Y1] [Inhabited Y2]
    {D : ℕ} {A : Set (ℕ → CommGraph)} {φ : Formula X1 X2 Y1 Y2}
    {B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))} {Qlive : Set QB}
    (hB : IsBlockAutomaton A φ D B Qlive)
    {t0 : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)}
    (ht0 : IsUncompressedComponentTree B Qlive t0) (hlive0 : ([] : List CommGraph) ∈ Pref A)
    {ws : List (Fin D → Signal X1 X2)} {u : Fin D → Signal X1 X2}
    (hl_next : graphOfHist (blockConcat (ws ++ [u])) ∈ Pref A) :
    ∃ i < t0.nChildren (treeNodeOf hB ht0 hlive0 ws),
      treeNodeOf hB ht0 hlive0 (ws ++ [u]) = treeNodeOf hB ht0 hlive0 ws ++ [i] ∧
      treeState hB ht0 hlive0 (ws ++ [u]) =
        (t0.label (treeNodeOf hB ht0 hlive0 ws)).qLam B (blockConcat ws) u := by
  have hinit_live : B.init ∈ Qlive := (reachableInB_live hB (reachableInB_zero B)).mpr hlive0
  have hl_ws : graphOfHist (blockConcat ws) ∈ Pref A := by
    rw [blockConcat_append_singleton] at hl_next
    have hcat : graphOfHist (blockConcat ws) ++ graphOfHist (List.ofFn u) ∈ Pref A := by
      simpa [graphOfHist] using hl_next
    exact (mem_pref_prefix hcat).1
  obtain ⟨hv_next, hlen_next, hmem_next⟩ := treeNodeOf_spec hB ht0 hlive0 hl_next
  set a_next := treeNodeOf hB ht0 hlive0 (ws ++ [u])
  cases ha_next_eq : a_next using List.reverseRecOn with
  | nil => simp [ha_next_eq] at hlen_next
  | append_singleton a_par i =>
    rw [ha_next_eq] at hv_next hlen_next hmem_next
    obtain ⟨hv_par, hi_lt⟩ := valid_append_singleton.mp hv_next
    have hlen_par : a_par.length = ws.length := by simpa using hlen_next
    obtain ⟨hcomp, hstate_eq⟩ := (ht0.2.2 a_par hv_par).2.1 i hi_lt
    have hin_live : blockConcat (ws ++ [u]) ∈ (t0.label a_par).liveExt B Qlive :=
      (isComponentOf_mem hcomp).2 hmem_next
    rcases hin_live with ⟨e, he_mem, u', heq_h, _⟩
    rcases he_mem with ⟨se, hse⟩
    have hlen_e : e.length = a_par.length * D :=
      (uncomp_node_inv ht0 hinit_live a_par hv_par e se hse).1.1
    rw [blockConcat_append_singleton] at heq_h hmem_next
    have he_eq : blockConcat ws = e := by
      have htake := congrArg (List.take (ws.length * D)) heq_h
      have hl1 : (blockConcat ws).length = ws.length * D := blockConcat_length ws
      have hl2 : e.length = ws.length * D := hlen_e.trans (hlen_par ▸ rfl)
      rwa [← hl1, List.take_left, hl1, ← hl2, List.take_left] at htake
    subst he_eq
    have hu_list : List.ofFn u = List.ofFn u' := List.append_cancel_left heq_h
    have hu_eq : u = u' := by
      funext j
      have hget := congrArg (fun l => l[j.val]?) hu_list
      simpa using hget
    subst hu_eq
    have ha_par_eq : a_par = treeNodeOf hB ht0 hlive0 ws := by
      have hspec_ws := treeNodeOf_spec hB ht0 hlive0 hl_ws
      exact uncomp_nodes_eq_of_view ht0 hinit_live hv_par hspec_ws.1
        (hlen_par.trans hspec_ws.2.1.symm) ⟨se, hse⟩ hspec_ws.2.2 (Or.inl rfl)
    subst ha_par_eq
    refine ⟨i, hi_lt, rfl, ?_⟩
    rcases hmem_next with ⟨s_next, hs_next⟩
    have hst_inv := (uncomp_node_inv ht0 hinit_live _ hv_next _ s_next hs_next).2.2
    have hs_eq := hstate_eq _ s_next hs_next (blockConcat ws) ⟨se, hse⟩ u rfl
    change (t0.label a_next).state B.init (blockConcat (ws ++ [u])) = _
    rw [ha_next_eq, blockConcat_append_singleton, hst_inv, hs_eq]

lemma treeState_parity {X1 X2 Y1 Y2 QB : Type}
    [DecidableEq X1] [DecidableEq X2] [Inhabited X1] [Inhabited X2] [Inhabited Y1] [Inhabited Y2]
    {D : ℕ} {A : Set (ℕ → CommGraph)} {φ : Formula X1 X2 Y1 Y2}
    {B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))} {Qlive : Set QB}
    (hB : IsBlockAutomaton A φ D B Qlive)
    {t0 : LabeledTree (NodeLabel X1 X2 Y1 Y2 QB)}
    (ht0 : IsUncompressedComponentTree B Qlive t0) (hacc0 : IsAcceptingTree B t0)
    (hlive0 : ([] : List CommGraph) ∈ Pref A)
    (word : ℕ → (Fin D → Signal X1 X2))
    (hlive : ∀ n, graphOfHist (blockConcat (pre word n)) ∈ Pref A) :
    ParityCond (fun n => B.prio (treeState hB ht0 hlive0 (pre word n))) := by
  let a : ℕ → List ℕ := fun n => treeNodeOf hB ht0 hlive0 (pre word n)
  let e : ℕ → List (Signal X1 X2) := fun n => blockConcat (pre word n)
  have hpre_succ : ∀ n, pre word (n + 1) = pre word n ++ [word n] := by
    intro n
    apply List.ext_getElem
    · simp [pre]
    · intro i hi1 hi2
      simp only [pre, List.length_ofFn] at hi1
      simp only [pre]
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi1) with hlt | rfl
      · rw [List.getElem_ofFn, List.getElem_append_left (by simp [hlt]), List.getElem_ofFn]
      · rw [List.getElem_ofFn, List.getElem_append_right (by simp), List.getElem_singleton]
  have ha0 : a 0 = [] := by
    have h0 : (a 0).length = (pre word 0).length := (treeNodeOf_spec hB ht0 hlive0 (hlive 0)).2.1
    exact List.eq_nil_of_length_eq_zero (h0.trans (by simp [pre]))
  have ha_step : ∀ n, t0.Valid (a n) ∧ ∃ i, a (n + 1) = a n ++ [i] := by
    intro n
    refine ⟨(treeNodeOf_spec hB ht0 hlive0 (hlive n)).1, ?_⟩
    have hl1 : graphOfHist (blockConcat (pre word n ++ [word n])) ∈ Pref A := by
      rw [← hpre_succ n]
      exact hlive (n + 1)
    obtain ⟨i, _, heq_a, _⟩ := treeNodeOf_append_singleton hB ht0 hlive0 hl1
    exact ⟨i, by dsimp only [a]; rwa [hpre_succ n]⟩
  have he0 : e 0 = [] := by simp [e, pre]
  have he_step : ∀ n, e (n + 1) = e n ++ List.ofFn (word n) := by
    intro n
    dsimp only [e]
    rw [hpre_succ n, blockConcat_append_singleton]
  have he_mem : ∀ n, e n ∈ (t0.label (a n)).edges :=
    fun n => (treeNodeOf_spec hB ht0 hlive0 (hlive n)).2.2
  exact hacc0 a e word ha0 ha_step he0 he_step he_mem

lemma getD_eq_getElem {α : Type} (l : List α) (d : α) (i : ℕ) (hi : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

lemma not_parityCond_and_oddParityCond (c : ℕ → ℕ) :
    ¬ (ParityCond c ∧ OddParityCond c) := by
  rintro ⟨⟨p, hp_even, hp_freq, hp_ev⟩, ⟨q, hq_odd, hq_freq, hq_ev⟩⟩
  obtain ⟨n1, hn1_eq, hn1_le⟩ := (hq_freq.and_eventually hp_ev).exists
  obtain ⟨n2, hn2_eq, hn2_le⟩ := (hp_freq.and_eventually hq_ev).exists
  have hpq : p = q := by omega
  subst hpq
  rcases hp_even with ⟨k, rfl⟩
  rcases hq_odd with ⟨l, hl⟩
  omega

lemma myPow_eq (b e : ℕ) : myPow b e = b ^ e := by
  unfold myPow
  induction e with
  | zero => simp
  | succ e ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih, pow_succ]

@[simp] lemma andBool_eq (a b : Bool) : andBool a b = (a && b) := by cases a <;> cases b <;> rfl

@[simp] lemma orBool_eq (a b : Bool) : orBool a b = (a || b) := by cases a <;> cases b <;> rfl

@[simp] lemma notBool_eq (a : Bool) : notBool a = !a := by cases a <;> rfl

@[simp] lemma cIdxOf_nil {α : Type} [DecidableEq α] (x : α) : cIdxOf ([] : List α) x = 0 := rfl

@[simp] lemma cIdxOf_cons {α : Type} [DecidableEq α] (y : α) (ys : List α) (x : α) :
    cIdxOf (y :: ys) x = if x = y then 0 else cIdxOf ys x + 1 := rfl

lemma cIdxOf_lt_and_getElem {α : Type} [DecidableEq α] {xs : List α} {x : α} (hx : x ∈ xs) :
    ∃ hlt : cIdxOf xs x < xs.length, xs[cIdxOf xs x]'hlt = x := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    by_cases hxy : x = y
    · subst hxy
      exact ⟨by simp, by simp⟩
    · rcases List.mem_cons.mp hx with rfl | htl
      · exact False.elim (hxy rfl)
      · obtain ⟨hlt, heq⟩ := ih htl
        have hc : cIdxOf (y :: ys) x = cIdxOf ys x + 1 := by simp [hxy]
        refine ⟨by rw [hc]; exact Nat.succ_lt_succ hlt, ?_⟩
        simp only [hc, List.getElem_cons_succ, heq]

lemma sigCard_pos (I : Instance) : 0 < sigCard I := by unfold sigCard; positivity

lemma decGraph_idx_mod (s : ℕ) : (decGraph s).idx = s % 3 := by
  unfold decGraph
  have hlt : s % 3 < 3 := Nat.mod_lt _ (by decide)
  set r := s % 3
  interval_cases r <;> rfl

lemma encSigTyped_lt (I : Instance) (s : Signal I.X1 I.X2) : encSigTyped I s < sigCard I := by
  rcases s with ⟨x1, x2, g⟩
  unfold encSigTyped sigCard
  have hg : g.idx < 3 := by cases g <;> decide
  have h1 : x1.val + 1 ≤ I.k1 + 1 := x1.isLt
  have h12 : x1.val * (I.k2 + 1) + x2.val < (I.k1 + 1) * (I.k2 + 1) := by
    calc
      x1.val * (I.k2 + 1) + x2.val < x1.val * (I.k2 + 1) + (I.k2 + 1) :=
        Nat.add_lt_add_left x2.isLt _
      _ = (x1.val + 1) * (I.k2 + 1) := by ring
      _ ≤ (I.k1 + 1) * (I.k2 + 1) := Nat.mul_le_mul_right _ h1
  have h12' : x1.val * (I.k2 + 1) + x2.val + 1 ≤ (I.k1 + 1) * (I.k2 + 1) := h12
  calc
    (x1.val * (I.k2 + 1) + x2.val) * 3 + g.idx
      < (x1.val * (I.k2 + 1) + x2.val) * 3 + 3 := Nat.add_lt_add_left hg _
    _ = (x1.val * (I.k2 + 1) + x2.val + 1) * 3 := by ring
    _ ≤ ((I.k1 + 1) * (I.k2 + 1)) * 3 := Nat.mul_le_mul_right 3 h12'

lemma decSigFields_encSigTyped (I : Instance) (s : Signal I.X1 I.X2) :
    decSigX1 I (encSigTyped I s) = s.1.val ∧
      decSigX2 I (encSigTyped I s) = s.2.1.val ∧
      decSigG (encSigTyped I s) = s.2.2.idx ∧
      decGraph (encSigTyped I s) = s.2.2 := by
  rcases s with ⟨x1, x2, g⟩
  have hg_lt : g.idx < 3 := by cases g <;> decide
  have hdiv3 : ((x1.val * (I.k2 + 1) + x2.val) * 3 + g.idx) / 3 =
      x1.val * (I.k2 + 1) + x2.val := by
    rw [Nat.mul_comm _ 3, Nat.add_comm, Nat.add_mul_div_left _ _ (by decide : 0 < 3),
      Nat.div_eq_of_lt hg_lt, zero_add]
  have hmod3 : ((x1.val * (I.k2 + 1) + x2.val) * 3 + g.idx) % 3 = g.idx := by
    rw [Nat.mul_comm _ 3, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hg_lt]
  have hdivK2 : (x1.val * (I.k2 + 1) + x2.val) / (I.k2 + 1) = x1.val := by
    rw [Nat.mul_comm x1.val _, Nat.add_comm, Nat.add_mul_div_left _ _ (Nat.succ_pos _),
      Nat.div_eq_of_lt x2.isLt, zero_add]
  have hmodK2 : (x1.val * (I.k2 + 1) + x2.val) % (I.k2 + 1) = x2.val := by
    rw [Nat.mul_comm x1.val _, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x2.isLt]
  refine ⟨?_, ?_, hmod3, ?_⟩
  · unfold decSigX1 encSigTyped; dsimp only; rw [hdiv3, hdivK2, Nat.mod_eq_of_lt x1.isLt]
  · unfold decSigX2 encSigTyped; dsimp only; rw [hdiv3, hmodK2]
  · unfold decGraph encSigTyped; dsimp only; rw [hmod3]; cases g <;> rfl

lemma decSigTyped_encSigTyped (I : Instance) (s : Signal I.X1 I.X2) :
    decSigTyped I (encSigTyped I s) = s := by
  obtain ⟨hx1, hx2, _, hg⟩ := decSigFields_encSigTyped I s
  rcases s with ⟨x1, x2, g⟩
  unfold decSigTyped
  ext <;> simp [hx1, hx2, hg]

lemma encSigTyped_decSigTyped (I : Instance) {n : ℕ} (hn : n < sigCard I) :
    encSigTyped I (decSigTyped I n) = n := by
  unfold encSigTyped decSigTyped
  dsimp only
  rw [decGraph_idx_mod]
  unfold decSigX1 decSigX2
  unfold sigCard at hn
  have hdiv3_lt : n / 3 < (I.k1 + 1) * (I.k2 + 1) :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 3)).mpr hn
  have hdivK2_lt : (n / 3) / (I.k2 + 1) < I.k1 + 1 :=
    (Nat.div_lt_iff_lt_mul (show 0 < I.k2 + 1 from Nat.succ_pos _)).mpr hdiv3_lt
  rw [Nat.mod_eq_of_lt hdivK2_lt]
  have h1 := Nat.div_add_mod (n / 3) (I.k2 + 1)
  have h2 := Nat.div_add_mod n 3
  linarith

@[simp] lemma decHist_encHist (I : Instance) (h : List (Signal I.X1 I.X2)) :
    decHist I (encHist I h) = h := by
  simp [decHist, encHist, List.map_map, Function.comp_def, decSigTyped_encSigTyped]

lemma encHist_decHist (I : Instance) {w : List ℕ} (hw : ∀ x ∈ w, x < sigCard I) :
    encHist I (decHist I w) = w := by
  unfold encHist decHist
  induction w with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    rw [encSigTyped_decSigTyped I (hw x (List.mem_cons.mpr (Or.inl rfl))),
      ih (fun y hy => hw y (List.mem_cons_of_mem _ hy))]

@[simp] lemma decBlock_encBlock (I : Instance) {D : ℕ} (u : Fin D → Signal I.X1 I.X2) :
    decBlock I D (encBlock I u) = u := by
  funext t
  unfold decBlock encBlock encHist
  rw [getD_eq_getElem _ 0 t.val (by simp [t.isLt])]
  simp [decSigTyped_encSigTyped]

lemma ofFn_decBlock (I : Instance) {D : ℕ} {uNat : List ℕ} (hlen : uNat.length = D) :
    List.ofFn (decBlock I D uNat) = decHist I uNat := by
  apply List.ext_getElem
  · simp [decHist, hlen]
  · intro i hi1 hi2
    simp only [List.getElem_ofFn, decBlock, decHist, List.getElem_map]
    rw [getD_eq_getElem uNat 0 i (by simpa [decHist] using hi2)]

lemma mem_nonemptyExtWords_iff (I : Instance) (D : ℕ) (w : List ℕ) :
    w ∈ nonemptyExtWords I D ↔ 1 ≤ w.length ∧ w.length ≤ D ∧ ∀ x ∈ w, x < sigCard I := by
  simp only [nonemptyExtWords, List.mem_flatMap, List.mem_map, List.mem_range, mem_wordsOf_iff]
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, hlen, hall⟩
    exact ⟨by omega, by omega, hall⟩
  · rintro ⟨h1, h2, hall⟩
    exact ⟨w.length, ⟨w.length - 1, by omega, by omega⟩, rfl, hall⟩

lemma mem_fullBlocks_iff (I : Instance) (D : ℕ) (u : List ℕ) :
    u ∈ fullBlocks I D ↔ u.length = D ∧ ∀ x ∈ u, x < sigCard I := by
  simp [fullBlocks, mem_wordsOf_iff]

lemma ctxBlockCard_pos (c : SymCtx) : 0 < ctxBlockCard c := by
  unfold ctxBlockCard; rw [myPow_eq]; exact Nat.pow_pos (sigCard_pos (ctxI c))

lemma ctxBRed_pos (c : SymCtx) : 0 < ctxBRed c := by
  unfold ctxBRed
  rw [myPow_eq]
  exact Nat.mul_pos (Nat.pow_pos (by unfold ctxQBCard; omega)) (ctxBlockCard_pos c)

lemma ctxBFull_pos (c : SymCtx) : 0 < ctxBFull c :=
  Nat.mul_pos (ctxBRed_pos c) (ctxBlockCard_pos c)

lemma mem_allSymPos_iff (c : SymCtx) (pos : SymPosCode) :
    pos ∈ allSymPos c ↔
      1 ≤ pos.1 ∧ pos.1 ≤ ctxBFull c ∧
        pos.2.1.length = pos.1 * pos.1 ∧
        pos.2.2.1.length = pos.1 * pos.1 ∧
        pos.2.2.2.length = pos.1 ∧
        (∀ s ∈ pos.2.2.2, s < ctxQBCard c) := by
  rcases pos with ⟨k, e1, e2, st⟩
  simp only [allSymPos, List.mem_flatMap, List.mem_map, List.mem_range, mem_wordsOf_iff,
    List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨_, ⟨k0, hk0, rfl⟩, _, ⟨he1, _⟩, _, ⟨he2, _⟩, _, ⟨hst, hst_lt⟩, heq⟩
    rcases Prod.mk.inj heq with ⟨rfl, heq2⟩
    rcases Prod.mk.inj heq2 with ⟨rfl, heq3⟩
    rcases Prod.mk.inj heq3 with ⟨rfl, rfl⟩
    exact ⟨by omega, by omega, he1, he2, hst, hst_lt⟩
  · rintro ⟨hk1, hk2, he1, he2, hst, hst_lt⟩
    refine ⟨k, ⟨k - 1, by omega, by omega⟩, e1, ⟨he1, fun b _ => by cases b <;> simp⟩,
      e2, ⟨he2, fun b _ => by cases b <;> simp⟩, st, ⟨hst, hst_lt⟩, rfl⟩

lemma mem_allSymActsFor_iff (c : SymCtx) (pos : SymPosCode) (act : SymActCode) :
    act ∈ allSymActsFor c pos ↔
      act.1.length = pos.1 ∧ (∀ r ∈ act.1, r < pos.1) ∧
        act.2.1.length = pos.1 * (nonemptyExtWords (ctxI c) (ctxD c)).length ∧
        (∀ y ∈ act.2.1, y < (ctxI c).m1 + 1) ∧
        act.2.2.length = pos.1 * (nonemptyExtWords (ctxI c) (ctxD c)).length ∧
        (∀ y ∈ act.2.2, y < (ctxI c).m2 + 1) := by
  rcases act with ⟨rList, o1, o2⟩
  simp only [allSymActsFor, List.mem_flatMap, List.mem_map, List.mem_range, mem_wordsOf_iff]
  constructor
  · rintro ⟨_, ⟨hr1, hr2⟩, _, ⟨ho1_l, ho1_v⟩, _, ⟨ho2_l, ho2_v⟩, heq⟩
    rcases Prod.mk.inj heq with ⟨rfl, heq2⟩
    rcases Prod.mk.inj heq2 with ⟨rfl, rfl⟩
    exact ⟨hr1, hr2, ho1_l, ho1_v, ho2_l, ho2_v⟩
  · rintro ⟨hr1, hr2, ho1_l, ho1_v, ho2_l, ho2_v⟩
    exact ⟨rList, ⟨hr1, hr2⟩, o1, ⟨ho1_l, ho1_v⟩, o2, ⟨ho2_l, ho2_v⟩, rfl⟩

def toBlocksList {X1 X2 : Type} [Inhabited X1] [Inhabited X2] (D n : ℕ)
    (h : List (Signal X1 X2)) : List (Fin D → Signal X1 X2) :=
  (List.range n).map fun k i => h.getD (k * D + i.val) (default, default, .both)

lemma toBlocksList_blockConcat {X1 X2 : Type} [Inhabited X1] [Inhabited X2] {D : ℕ}
    (ws : List (Fin D → Signal X1 X2)) :
    toBlocksList D ws.length (blockConcat ws) = ws := by
  induction ws using List.reverseRecOn with
  | nil => simp [toBlocksList]
  | append_singleton ws u ih =>
    have hlen_ws : (blockConcat ws).length = ws.length * D := blockConcat_length ws
    simp only [List.length_append, List.length_singleton, toBlocksList, List.range_succ,
      List.map_append, List.map_singleton, blockConcat_append_singleton]
    congr 1
    · conv_rhs => rw [← ih]
      unfold toBlocksList
      apply List.map_congr_left
      intro k hk
      have hk_lt : k < ws.length := List.mem_range.mp hk
      funext i
      have hidx_lt : k * D + i.val < (blockConcat ws).length := by
        rw [hlen_ws]
        have h1 : k + 1 ≤ ws.length := hk_lt
        calc
          k * D + i.val < k * D + D := Nat.add_lt_add_left i.isLt _
          _ = (k + 1) * D := by ring
          _ ≤ ws.length * D := Nat.mul_le_mul_right D h1
      rw [getD_eq_getElem _ _ _ (by simp; omega), List.getElem_append_left hidx_lt,
        getD_eq_getElem _ _ _ hidx_lt]
    · congr 1
      funext i
      have hge : (blockConcat ws).length ≤ ws.length * D + i.val := by rw [hlen_ws]; omega
      rw [getD_eq_getElem _ _ _ (by simp [hlen_ws, i.isLt]), List.getElem_append_right hge]
      simp [hlen_ws]

lemma blockConcat_injective {X1 X2 : Type} [Inhabited X1] [Inhabited X2] {D : ℕ} (hD : 1 ≤ D) :
    Function.Injective (blockConcat (X1 := X1) (X2 := X2) (D := D)) := by
  intro ws1 ws2 heq
  have hlen_eq : ws1.length = ws2.length := by
    have hl := congrArg List.length heq
    rw [blockConcat_length, blockConcat_length] at hl
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < D) hl
  have htb := congrArg (toBlocksList D ws1.length) heq
  rwa [toBlocksList_blockConcat, hlen_eq, toBlocksList_blockConcat] at htb

lemma flatMap_range_sq_getD (k : ℕ) (f : ℕ → ℕ → Bool) :
    ((List.range k).flatMap fun a => (List.range k).map (f a)).length = k * k ∧
    ∀ i j : Fin k,
      ((List.range k).flatMap fun a => (List.range k).map (f a)).getD (i.val * k + j.val) false =
        f i.val j.val := by
  refine ⟨by simp [List.length_flatMap, List.map_const'], fun i j => ?_⟩
  have hrec : ∀ (R : ℕ) (r : ℕ) (hr : r < R),
      ((List.range R).flatMap fun a => (List.range k).map (f a)).getD (r * k + j.val) false =
        f r j.val := by
    intro R r hr
    induction R with
    | zero => cases hr
    | succ R ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have hlp : ((List.range R).flatMap fun a => (List.range k).map (f a)).length = R * k := by
        simp [List.length_flatMap, List.map_const']
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hr) with rfl | hr_lt
      · rw [getD_eq_getElem _ false _ (by simp [hlp, j.isLt]), List.getElem_append_right (by omega)]
        simp [hlp]
      · have hlt_p : r * k + j.val < R * k := by
          have h1 : r + 1 ≤ R := hr_lt
          calc r * k + j.val < r * k + k := Nat.add_lt_add_left j.isLt _
            _ = (r + 1) * k := by ring
            _ ≤ R * k := Nat.mul_le_mul_right k h1
        rw [getD_eq_getElem _ false _ (by simp [hlp]; omega),
          List.getElem_append_left (by omega), ← getD_eq_getElem _ false _ (by omega)]
        exact ih hr_lt
  exact hrec k i.val i.isLt

lemma flatMap_range_mul_getD (k NW : ℕ) (g : Fin k → ℕ → ℕ) :
    ((List.range k).flatMap fun iv => (List.range NW).map fun wi =>
      if h : iv < k then g ⟨iv, h⟩ wi else 0).length = k * NW ∧
    ∀ (i : Fin k) (wi : ℕ), wi < NW →
      ((List.range k).flatMap fun iv => (List.range NW).map fun wi =>
        if h : iv < k then g ⟨iv, h⟩ wi else 0).getD (i.val * NW + wi) 0 = g i wi := by
  refine ⟨by simp [List.length_flatMap, List.map_const'], fun i wi hwi => ?_⟩
  have hrec : ∀ (R r : ℕ) (hr : r < R),
      ((List.range R).flatMap fun iv => (List.range NW).map fun w0 =>
        if h : iv < k then g ⟨iv, h⟩ w0 else 0).getD (r * NW + wi) 0 =
        (if h : r < k then g ⟨r, h⟩ wi else 0) := by
    intro R r hr
    induction R with
    | zero => cases hr
    | succ R ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have hlp : ((List.range R).flatMap fun iv => (List.range NW).map fun w0 =>
          if h : iv < k then g ⟨iv, h⟩ w0 else 0).length = R * NW := by
        simp [List.length_flatMap, List.map_const']
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hr) with rfl | hr_lt
      · rw [getD_eq_getElem _ 0 _ (by simp [hlp, hwi]), List.getElem_append_right (by omega)]
        simp [hlp]
      · have hlt_p : r * NW + wi < R * NW := by
          have h1 : r + 1 ≤ R := hr_lt
          calc r * NW + wi < r * NW + NW := Nat.add_lt_add_left hwi _
            _ = (r + 1) * NW := by ring
            _ ≤ R * NW := Nat.mul_le_mul_right NW h1
        rw [getD_eq_getElem _ 0 _ (by simp [hlp]; omega),
          List.getElem_append_left (by omega), ← getD_eq_getElem _ 0 _ (by omega)]
        exact ih hr_lt
  rw [hrec k i.val i.isLt, dif_pos i.isLt]

abbrev UncompPosData (I : Instance) (D B_full B_red : ℕ)
    (liveBlk : List (Fin D → Signal I.X1 I.X2) → Prop)
    {Q_sz : ℕ} (treeSt : List (Fin D → Signal I.X1 I.X2) → Fin Q_sz)
    {K_p : ℕ} (rkFn : List (Fin D → Signal I.X1 I.X2) → Lex (Fin K_p → Ordinal.{0}))
    (n : ℕ) : Type :=
  { d : Σ k : ℕ, (Fin k → List (Fin D → Signal I.X1 I.X2)) × (Fin k → Fin k) //
    1 ≤ d.1 ∧ d.1 ≤ B_full ∧
    (∀ i : Fin d.1, (d.2.1 i).length = n) ∧
    Function.Injective d.2.1 ∧
    (∀ i : Fin d.1, liveBlk (d.2.1 i)) ∧
    (∀ i j : Fin d.1, Relation.ReflTransGen
      (fun x y : Fin d.1 => EdgeAdj (blockConcat (d.2.1 x)) (blockConcat (d.2.1 y))) i j) ∧
    (∀ i : Fin d.1, d.2.2 (d.2.2 i) = d.2.2 i) ∧
    (Finset.univ.filter (fun i : Fin d.1 => d.2.2 i = i)).card ≤ B_red ∧
    (∀ i : Fin d.1, treeSt (d.2.1 (d.2.2 i)) = treeSt (d.2.1 i)) ∧
    (∀ (i j : Fin d.1) (p : Proc),
      viewOf p (blockConcat (d.2.1 i)) = viewOf p (blockConcat (d.2.1 j)) →
        viewOf p (blockConcat (d.2.1 (d.2.2 i))) = viewOf p (blockConcat (d.2.1 (d.2.2 j)))) ∧
    (∀ m : ℕ, n = m + 1 → ∀ i : Fin d.1,
      ∃ (ws_c : List (Fin D → Signal I.X1 I.X2)) (u_last : Fin D → Signal I.X1 I.X2),
        d.2.1 i = (d.2.1 i).take m ++ [u_last] ∧
        d.2.1 (d.2.2 i) = ws_c ++ [u_last] ∧
        rkFn ws_c ≤ rkFn ((d.2.1 i).take m)) }

lemma uncomp_mk_child_rFn (c : DPACode) (I : Instance) (D : ℕ) (hD : 1 ≤ D)
    (hCons : ∀ g ∈ Pref c.lang, ConsensusSolvableWithin Bool (leftQuot g c.lang) D)
    {Q_N : ℕ} (treeSt : List (Fin D → Signal I.X1 I.X2) → Fin (Q_N + 1))
    {K_prio : ℕ} (rkFn : List (Fin D → Signal I.X1 I.X2) → Lex (Fin (K_prio + 1) → Ordinal.{0}))
    (B_red : ℕ) (hBRed : (1 + (Q_N + 1)) ^ (sigCard I ^ D) * (sigCard I ^ D) = B_red)
    (m k : ℕ) (hk1 : 1 ≤ k)
    (blocks : Fin k → List (Fin D → Signal I.X1 I.X2))
    (hlen : ∀ i : Fin k, (blocks i).length = m + 1)
    (hinj : Function.Injective blocks)
    (hlive : ∀ i : Fin k, graphOfHist (blockConcat (blocks i)) ∈ Pref c.lang)
    (hconn : ∀ i j : Fin k, Relation.ReflTransGen
      (fun x y : Fin k => EdgeAdj (blockConcat (blocks x)) (blockConcat (blocks y))) i j) :
    ∃ rFn : Fin k → Fin k,
      (∀ i : Fin k, rFn (rFn i) = rFn i) ∧
      (Finset.univ.filter (fun i : Fin k => rFn i = i)).card ≤ B_red ∧
      (∀ i : Fin k, treeSt (blocks (rFn i)) = treeSt (blocks i)) ∧
      (∀ (i j : Fin k) (p : Proc),
        viewOf p (blockConcat (blocks i)) = viewOf p (blockConcat (blocks j)) →
          viewOf p (blockConcat (blocks (rFn i))) = viewOf p (blockConcat (blocks (rFn j)))) ∧
      (∀ m' : ℕ, m + 1 = m' + 1 → ∀ i : Fin k,
        ∃ (ws_c : List (Fin D → Signal I.X1 I.X2)) (u_last : Fin D → Signal I.X1 I.X2),
          blocks i = (blocks i).take m' ++ [u_last] ∧
          blocks (rFn i) = ws_c ++ [u_last] ∧
          rkFn ws_c ≤ rkFn ((blocks i).take m')) := by
  classical
  let H : Fin k → List (Signal I.X1 I.X2) := fun i => blockConcat (blocks i)
  have hH_inj : Function.Injective H := (blockConcat_injective hD).comp hinj
  let C : Finset (List (Signal I.X1 I.X2)) := Finset.univ.image H
  have hC_ne : C.Nonempty := ⟨H ⟨0, hk1⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have hC_len : ∀ h ∈ C, h.length = m * D + D := by
    intro h hh
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hh
    dsimp only [H]
    rw [blockConcat_length, hlen i, Nat.succ_mul]
  have hC_live : ∀ h ∈ C, graphOfHist h ∈ Pref c.lang := by
    intro h hh
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hh
    exact hlive i
  have hC_conn : ∀ h1 ∈ C, ∀ h2 ∈ C,
      Relation.ReflTransGen (fun x y => x ∈ C ∧ y ∈ C ∧ EdgeAdj x y) h1 h2 := by
    intro h1 hh1 h2 hh2
    obtain ⟨i1, -, rfl⟩ := Finset.mem_image.mp hh1
    obtain ⟨i2, -, rfl⟩ := Finset.mem_image.mp hh2
    clear hh1 hh2
    have hp := hconn i1 i2
    induction hp with
    | refl => exact .refl
    | @tail b c0 _ hedge ih =>
      exact ih.tail ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
        Finset.mem_image_of_mem _ (Finset.mem_univ _), hedge⟩
  let stHist : List (Signal I.X1 I.X2) → Fin (Q_N + 1) :=
    fun h => treeSt (toBlocksList D (m + 1) h)
  have hstHist_H : ∀ i : Fin k, stHist (H i) = treeSt (blocks i) := by
    intro i
    dsimp only [stHist, H]
    rw [← hlen i, toBlocksList_blockConcat]
  let R_roots : Finset (List (Signal I.X1 I.X2)) := C.image (List.take (m * D))
  let clsOf (T : (Fin D → Signal I.X1 I.X2) → Option (Fin (Q_N + 1))) :
      Finset (List (Signal I.X1 I.X2)) :=
    R_roots.filter fun a' => endTableOf D C stHist a' = T
  let bestFor (T : (Fin D → Signal I.X1 I.X2) → Option (Fin (Q_N + 1))) :
      List (Signal I.X1 I.X2) :=
    if hne : (clsOf T).Nonempty then
      (Finset.exists_min_image (clsOf T) (fun a' => rkFn (toBlocksList D m a')) hne).choose
    else []
  let rep : List (Signal I.X1 I.X2) → List (Signal I.X1 I.X2) :=
    fun a => bestFor (endTableOf D C stHist a)
  have hrep_spec : ∀ a ∈ R_roots,
      rep a ∈ R_roots ∧
      endTableOf D C stHist (rep a) = endTableOf D C stHist a ∧
      rkFn (toBlocksList D m (rep a)) ≤ rkFn (toBlocksList D m a) := by
    intro a ha
    have ha_cls : a ∈ clsOf (endTableOf D C stHist a) := Finset.mem_filter.mpr ⟨ha, rfl⟩
    have hne : (clsOf (endTableOf D C stHist a)).Nonempty := ⟨a, ha_cls⟩
    dsimp only [rep, bestFor]
    rw [dif_pos hne]
    obtain ⟨hmem_c, hmin_c⟩ :=
      (Finset.exists_min_image (clsOf (endTableOf D C stHist a))
        (fun a' => rkFn (toBlocksList D m a')) hne).choose_spec
    obtain ⟨hr_mem, hr_tbl⟩ := Finset.mem_filter.mp hmem_c
    exact ⟨hr_mem, hr_tbl, hmin_c a ha_cls⟩
  have hrep_const : ∀ a1 ∈ R_roots, ∀ a2 ∈ R_roots,
      endTableOf D C stHist a1 = endTableOf D C stHist a2 → rep a1 = rep a2 :=
    fun _ _ _ _ heq => congrArg bestFor heq
  obtain ⟨hf_mem, hf_idem, hf_st, hf_views, hf_card⟩ :=
    endpoint_table_folding hD hCons (m * D) hC_ne hC_len hC_live hC_conn stHist rep
      (fun a ha => (hrep_spec a ha).1)
      (fun a ha => (hrep_spec a ha).2.1)
      hrep_const
  let foldEdge := fun h : List (Signal I.X1 I.X2) => rep (h.take (m * D)) ++ h.drop (m * D)
  have hex_r : ∀ i : Fin k, ∃ j : Fin k, H j = foldEdge (H i) := by
    intro i
    have hmem := hf_mem (H i) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
    exact ⟨j, hj⟩
  let rFn : Fin k → Fin k := fun i => (hex_r i).choose
  have hrFn_H : ∀ i : Fin k, H (rFn i) = foldEdge (H i) := fun i => (hex_r i).choose_spec
  refine ⟨rFn, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    apply hH_inj
    rw [hrFn_H, hrFn_H]
    dsimp only [foldEdge]
    exact hf_idem (H i) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  · have hsub_card : (Finset.univ.filter (fun i : Fin k => rFn i = i)).card ≤
        (C.image foldEdge).card := by
      have hinj_img : ∀ i ∈ Finset.univ.filter (fun i : Fin k => rFn i = i),
          H i ∈ C.image foldEdge := by
        intro i hi
        have hri : rFn i = i := (Finset.mem_filter.mp hi).2
        refine Finset.mem_image.mpr ⟨H i, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
        rw [← hrFn_H i, hri]
      exact Finset.card_le_card_of_injOn H hinj_img (fun a _ b _ heq => hH_inj heq)
    have hcard_eq : (1 + Fintype.card (Fin (Q_N + 1))) ^ (Fintype.card (Signal I.X1 I.X2) ^ D) *
        (Fintype.card (Signal I.X1 I.X2) ^ D) = B_red := by
      have hsig_card : Fintype.card (Signal I.X1 I.X2) = sigCard I := by
        have hc3 : Fintype.card CommGraph = 3 :=
          Fintype.card_congr commGraphEquivFin3 |>.trans (Fintype.card_fin 3)
        simp only [Signal, Fintype.card_prod, Fintype.card_fin, hc3, sigCard]
        ring
      rw [Fintype.card_fin, hsig_card, hBRed]
    exact le_trans hsub_card (hcard_eq ▸ hf_card)
  · intro i
    rw [← hstHist_H, ← hstHist_H, hrFn_H]
    exact hf_st (H i) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  · intro i j p hv
    change viewOf p (H (rFn i)) = viewOf p (H (rFn j))
    rw [hrFn_H, hrFn_H]
    exact hf_views (H i) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
      (H j) (Finset.mem_image_of_mem _ (Finset.mem_univ _)) p hv
  · intro m' hm_eq i
    cases Nat.succ.inj hm_eq
    let u_last := (blocks i)[m]'(by rw [hlen i]; omega)
    have hsplit_i : blocks i = (blocks i).take m ++ [u_last] := by
      conv_lhs => rw [← List.take_append_drop m (blocks i)]
      congr 1
      have hdrop_len : ((blocks i).drop m).length = 1 := by simp [hlen i]
      rcases List.length_eq_one_iff.mp hdrop_len with ⟨x, hx⟩
      have hget : ((blocks i).drop m)[0]'(by rw [hx]; simp) = x := by simp [hx]
      rw [hx, ← hget, List.getElem_drop]
      simp [u_last]
    have hHi_split : H i = blockConcat ((blocks i).take m) ++ List.ofFn u_last := by
      dsimp only [H]
      conv_lhs => rw [hsplit_i, blockConcat_append_singleton]
    have hlen_pre_m : (blockConcat ((blocks i).take m)).length = m * D := by
      rw [blockConcat_length, List.length_take, hlen i, min_eq_left (Nat.le_succ m)]
    have htake_Hi : (H i).take (m * D) = blockConcat ((blocks i).take m) := by
      rw [hHi_split, ← hlen_pre_m, List.take_left]
    have hdrop_Hi : (H i).drop (m * D) = List.ofFn u_last := by
      rw [hHi_split, ← hlen_pre_m, List.drop_left]
    have ha_in_roots : (H i).take (m * D) ∈ R_roots :=
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    obtain ⟨hrep_in_roots, _, hrk_le⟩ := hrep_spec ((H i).take (m * D)) ha_in_roots
    obtain ⟨h_src, hh_src_C, hrep_eq_take⟩ := Finset.mem_image.mp hrep_in_roots
    obtain ⟨j_src, -, rfl⟩ := Finset.mem_image.mp hh_src_C
    have hsplit_j : blocks j_src = (blocks j_src).take m ++ [(blocks j_src)[m]'(by rw [hlen j_src]; omega)] := by
      conv_lhs => rw [← List.take_append_drop m (blocks j_src)]
      congr 1
      have hdrop_len : ((blocks j_src).drop m).length = 1 := by simp [hlen j_src]
      rcases List.length_eq_one_iff.mp hdrop_len with ⟨x, hx⟩
      have hget : ((blocks j_src).drop m)[0]'(by rw [hx]; simp) = x := by simp [hx]
      rw [hx, ← hget, List.getElem_drop]
      simp
    have hHj_take : (H j_src).take (m * D) = blockConcat ((blocks j_src).take m) := by
      dsimp only [H]
      conv_lhs => rw [hsplit_j, blockConcat_append_singleton]
      have hl : (blockConcat ((blocks j_src).take m)).length = m * D := by
        rw [blockConcat_length, List.length_take, hlen j_src, min_eq_left (Nat.le_succ m)]
      rw [← hl, List.take_left]
    let ws_c := (blocks j_src).take m
    have hws_c_len : ws_c.length = m := by
      dsimp [ws_c]; rw [List.length_take, hlen j_src, min_eq_left (Nat.le_succ m)]
    have hrep_bc : rep ((H i).take (m * D)) = blockConcat ws_c :=
      hrep_eq_take.symm.trans hHj_take
    refine ⟨ws_c, u_last, hsplit_i, ?_, ?_⟩
    · apply blockConcat_injective hD
      rw [blockConcat_append_singleton]
      change H (rFn i) = blockConcat ws_c ++ List.ofFn u_last
      rw [hrFn_H, show foldEdge (H i) = rep ((H i).take (m * D)) ++ (H i).drop (m * D) from rfl,
        hrep_bc, hdrop_Hi]
    · have htb_c : toBlocksList D m (rep ((H i).take (m * D))) = ws_c := by
        have htb := toBlocksList_blockConcat ws_c
        rwa [hws_c_len, ← hrep_bc] at htb
      have htb_i : toBlocksList D m ((H i).take (m * D)) = (blocks i).take m := by
        have hli : ((blocks i).take m).length = m := by
          rw [List.length_take, hlen i, min_eq_left (Nat.le_succ m)]
        have htb := toBlocksList_blockConcat ((blocks i).take m)
        rwa [hli, ← htake_Hi] at htb
      rwa [htb_c, htb_i] at hrk_le

lemma exists_uncomp_sym_maps (E : Thm34Engine)
    (c : DPACode) (I : Instance) (D_m1 D : ℕ) (hD_def : D = D_m1 + 1)
    (φ : Formula ℕ ℕ ℕ ℕ)
    (res : GenDPACode × List Bool)
    (ctx : SymCtx) (hctx_def : ctx = (I, D_m1, res.1, res.2))
    (B : DPA (Fin (res.1.1 + 1)) (Fin D → Signal I.X1 I.X2 × (I.Y1 × I.Y2)))
    (Qlive : Set (Fin (res.1.1 + 1)))
    (hB_init : B.init.val = 0)
    (hB_step : ∀ (q : Fin (res.1.1 + 1)) (blk : Fin D → Signal I.X1 I.X2 × (I.Y1 × I.Y2)),
      (B.step q blk).val =
        (res.1.2.1.getD (q.val * (E.blockAlphaMinusOne I D + 1) +
          (E.encIOBlockTyped I D blk).val) 0) % (res.1.1 + 1))
    (hQlive_mem : ∀ q : Fin (res.1.1 + 1), q ∈ Qlive ↔ res.2.getD q.val false = true)
    (hB : IsBlockAutomaton c.lang (instFormulaOf I φ) D B Qlive)
    (hlive0 : ([] : List CommGraph) ∈ Pref c.lang)
    (t0 : LabeledTree (NodeLabel I.X1 I.X2 I.Y1 I.Y2 (Fin (res.1.1 + 1))))
    (ht0 : IsUncompressedComponentTree B Qlive t0)
    (liveBlk : List (Fin D → Signal I.X1 I.X2) → Prop)
    (hliveBlk_def : liveBlk = fun ws => graphOfHist (blockConcat ws) ∈ Pref c.lang)
    {K_prio : ℕ}
    (rkFn : List (Fin D → Signal I.X1 I.X2) → Lex (Fin (K_prio + 1) → Ordinal.{0})) :
    ∃ (symPosOf : ∀ {n : ℕ},
        UncompPosData I D (ctxBFull ctx) (ctxBRed ctx) liveBlk (treeState hB ht0 hlive0) rkFn n → SymPosCode)
      (symActOf : ∀ {n : ℕ},
        UncompPosData I D (ctxBFull ctx) (ctxBRed ctx) liveBlk (treeState hB ht0 hlive0) rkFn n → SymActCode),
      (∀ {n : ℕ} (pd : UncompPosData I D (ctxBFull ctx) (ctxBRed ctx) liveBlk (treeState hB ht0 hlive0) rkFn n),
        symPosOf pd =
          let k := pd.val.1
          let blocks := pd.val.2.1
          let e1 := (List.range k).flatMap fun a => (List.range k).map fun b =>
            if h : a < k ∧ b < k then
              decide (view1 (blockConcat (blocks ⟨a, h.1⟩)) = view1 (blockConcat (blocks ⟨b, h.2⟩)))
            else false
          let e2 := (List.range k).flatMap fun a => (List.range k).map fun b =>
            if h : a < k ∧ b < k then
              decide (view2 (blockConcat (blocks ⟨a, h.1⟩)) = view2 (blockConcat (blocks ⟨b, h.2⟩)))
            else false
          let st := (List.finRange k).map fun i => (treeState hB ht0 hlive0 (blocks i)).val
          (k, e1, e2, st)) ∧
      (∀ {n : ℕ} (pd : UncompPosData I D (ctxBFull ctx) (ctxBRed ctx) liveBlk (treeState hB ht0 hlive0) rkFn n),
        let pos := symPosOf pd
        let k := pd.val.1
        let blocks := pd.val.2.1
        pos ∈ allSymPos ctx ∧ pos.1 = k ∧
        (∀ i j : Fin k, eq1At pos i.val j.val =
          decide (view1 (blockConcat (blocks i)) = view1 (blockConcat (blocks j)))) ∧
        (∀ i j : Fin k, eq2At pos i.val j.val =
          decide (view2 (blockConcat (blocks i)) = view2 (blockConcat (blocks j)))) ∧
        (∀ i : Fin k, stateAt pos i.val = (treeState hB ht0 hlive0 (blocks i)).val)) ∧
      (∀ {n : ℕ} (pd : UncompPosData I D (ctxBFull ctx) (ctxBRed ctx) liveBlk (treeState hB ht0 hlive0) rkFn n),
        (symPosOf pd, symActOf pd) ∈ validSymLabels ctx ∧
        (fixedIdxs (symPosOf pd) (symActOf pd)).length ≤ ctxBRed ctx ∧
        (∀ i : Fin pd.val.1, (symActOf pd).1.getD i.val 0 = (pd.val.2.2 i).val) ∧
        ∀ i : Fin pd.val.1,
          treeNodeOf hB ht0 hlive0 (pd.val.2.1 i) =
            treeNodeOf hB ht0 hlive0 (pd.val.2.1 ⟨0, pd.property.1⟩)) ∧
      (∀ {n : ℕ} (pd : UncompPosData I D (ctxBFull ctx) (ctxBRed ctx) liveBlk (treeState hB ht0 hlive0) rkFn n)
        (i : Fin pd.val.1) (u : Fin D → Signal I.X1 I.X2),
        let next_q := symNextState E ctx (symPosOf pd) (symActOf pd) i.val (encBlock I u)
        ((res.2.getD next_q false = true) ↔ liveBlk (pd.val.2.1 i ++ [u])) ∧
        (liveBlk (pd.val.2.1 i ++ [u]) →
          next_q = (treeState hB ht0 hlive0 (pd.val.2.1 i ++ [u])).val)) ∧
      (∃ pd0 : UncompPosData I D (ctxBFull ctx) (ctxBRed ctx) liveBlk (treeState hB ht0 hlive0) rkFn 0,
        symPosOf pd0 = initSymPos) := by
  classical
  subst hD_def
  subst hctx_def
  subst hliveBlk_def
  let D := D_m1 + 1
  let ctx : SymCtx := (I, D_m1, res.1, res.2)
  have hinit_live : B.init ∈ Qlive := (reachableInB_live hB (reachableInB_zero B)).mpr hlive0
  let liveBlk : List (Fin D → Signal I.X1 I.X2) → Prop :=
    fun ws => graphOfHist (blockConcat ws) ∈ Pref c.lang
  let PosData := UncompPosData I D (ctxBFull ctx) (ctxBRed ctx) liveBlk
    (treeState hB ht0 hlive0) rkFn
  obtain ⟨symPosOf, hsymPosOf_def⟩ : ∃ f : ∀ {n : ℕ}, PosData n → SymPosCode,
      ∀ {n : ℕ} (pd : PosData n), f pd =
        let k := pd.val.1
        let blocks := pd.val.2.1
        let e1 := (List.range k).flatMap fun a => (List.range k).map fun b =>
          if h : a < k ∧ b < k then
            decide (view1 (blockConcat (blocks ⟨a, h.1⟩)) = view1 (blockConcat (blocks ⟨b, h.2⟩)))
          else false
        let e2 := (List.range k).flatMap fun a => (List.range k).map fun b =>
          if h : a < k ∧ b < k then
            decide (view2 (blockConcat (blocks ⟨a, h.1⟩)) = view2 (blockConcat (blocks ⟨b, h.2⟩)))
          else false
        let st := (List.finRange k).map fun i => (treeState hB ht0 hlive0 (blocks i)).val
        (k, e1, e2, st) := ⟨_, fun _ => rfl⟩
  have hsymPos_access : ∀ {n : ℕ} (pd : PosData n),
      let pos := symPosOf pd
      let k := pd.val.1
      let blocks := pd.val.2.1
      pos ∈ allSymPos ctx ∧ pos.1 = k ∧
      (∀ i j : Fin k, eq1At pos i.val j.val =
        decide (view1 (blockConcat (blocks i)) = view1 (blockConcat (blocks j)))) ∧
      (∀ i j : Fin k, eq2At pos i.val j.val =
        decide (view2 (blockConcat (blocks i)) = view2 (blockConcat (blocks j)))) ∧
      (∀ i : Fin k, stateAt pos i.val = (treeState hB ht0 hlive0 (blocks i)).val) := by
    intro n pd
    dsimp only
    rw [hsymPosOf_def pd]
    let k := pd.val.1
    let blocks := pd.val.2.1
    obtain ⟨hk1, hkB, _⟩ := pd.property
    refine ⟨?_, rfl, ?_, ?_, ?_⟩
    · rw [mem_allSymPos_iff]
      refine ⟨hk1, hkB, (flatMap_range_sq_getD k _).1, (flatMap_range_sq_getD k _).1, by simp, ?_⟩
      intro s hs
      simp only [List.mem_map, List.mem_finRange, true_and] at hs
      rcases hs with ⟨i, rfl⟩
      exact (treeState hB ht0 hlive0 (blocks i)).isLt
    · intro i j
      unfold eq1At
      dsimp only
      rw [(flatMap_range_sq_getD k _).2 i j, dif_pos ⟨i.isLt, j.isLt⟩]
    · intro i j
      unfold eq2At
      dsimp only
      rw [(flatMap_range_sq_getD k _).2 i j, dif_pos ⟨i.isLt, j.isLt⟩]
    · intro i
      unfold stateAt
      dsimp only
      rw [getD_eq_getElem _ 0 i.val (by simp [i.isLt])]
      simp
  let words := nonemptyExtWords I D
  let NW := words.length
  have hflat_kNW : ∀ (k : ℕ) (g : Fin k → ℕ → ℕ),
      ((List.range k).flatMap fun iv => (List.range NW).map fun wi =>
        if h : iv < k then g ⟨iv, h⟩ wi else 0).length = k * NW ∧
      ∀ (i : Fin k) (wi : ℕ), wi < NW →
        ((List.range k).flatMap fun iv => (List.range NW).map fun wi =>
          if h : iv < k then g ⟨iv, h⟩ wi else 0).getD (i.val * NW + wi) 0 = g i wi :=
    fun k g => flatMap_range_mul_getD k NW g
  obtain ⟨symActOf, hsymActOf_def⟩ : ∃ f : ∀ {n : ℕ}, PosData n → SymActCode,
      ∀ {n : ℕ} (pd : PosData n), f pd =
        let k := pd.val.1
        let blocks := pd.val.2.1
        let rFn := pd.val.2.2
        let a0 := treeNodeOf hB ht0 hlive0 (blocks ⟨0, pd.property.1⟩)
        let rList := (List.range k).map fun iv => if h : iv < k then (rFn ⟨iv, h⟩).val else 0
        let o1 := (List.range k).flatMap fun iv =>
          (List.range NW).map fun wi =>
            if h : iv < k then
              ((t0.label a0).lam1 (view1 (blockConcat (blocks ⟨iv, h⟩) ++ decHist I (words.getD wi [])))).val
            else 0
        let o2 := (List.range k).flatMap fun iv =>
          (List.range NW).map fun wi =>
            if h : iv < k then
              ((t0.label a0).lam2 (view2 (blockConcat (blocks ⟨iv, h⟩) ++ decHist I (words.getD wi [])))).val
            else 0
        (rList, o1, o2) := ⟨_, fun _ => rfl⟩
  have hsymAct_access : ∀ {n : ℕ} (pd : PosData n),
      let act := symActOf pd
      let k := pd.val.1
      let blocks := pd.val.2.1
      let a0 := treeNodeOf hB ht0 hlive0 (blocks ⟨0, pd.property.1⟩)
      act ∈ allSymActsFor ctx (symPosOf pd) ∧
      (∀ i : Fin k, act.1.getD i.val 0 = (pd.val.2.2 i).val) ∧
      (∀ (i : Fin k) (wi : ℕ), wi < NW →
        act.2.1.getD (i.val * NW + wi) 0 =
          ((t0.label a0).lam1 (view1 (blockConcat (blocks i) ++ decHist I (words.getD wi [])))).val) ∧
      (∀ (i : Fin k) (wi : ℕ), wi < NW →
        act.2.2.getD (i.val * NW + wi) 0 =
          ((t0.label a0).lam2 (view2 (blockConcat (blocks i) ++ decHist I (words.getD wi [])))).val) := by
    intro n pd
    let k := pd.val.1
    let blocks := pd.val.2.1
    let a0 := treeNodeOf hB ht0 hlive0 (blocks ⟨0, pd.property.1⟩)
    let g1 : Fin k → ℕ → ℕ := fun idx wi =>
      ((t0.label a0).lam1 (view1 (blockConcat (blocks idx) ++ decHist I (words.getD wi [])))).val
    let g2 : Fin k → ℕ → ℕ := fun idx wi =>
      ((t0.label a0).lam2 (view2 (blockConcat (blocks idx) ++ decHist I (words.getD wi [])))).val
    have hpos_k : (symPosOf pd).1 = k := (hsymPos_access pd).2.1
    have hctxI : ctxI ctx = I := rfl
    have hctxD : ctxD ctx = D := rfl
    dsimp only
    rw [hsymActOf_def pd]
    refine ⟨?_, ?_, (hflat_kNW k g1).2, (hflat_kNW k g2).2⟩
    · rw [mem_allSymActsFor_iff, hctxI, hctxD, hpos_k]
      dsimp only
      change _ ∧ _ ∧ _ = k * NW ∧ _ ∧ _ = k * NW ∧ _
      refine ⟨by simp [k], ?_, (hflat_kNW k g1).1, ?_, (hflat_kNW k g2).1, ?_⟩
      · intro r hr
        simp only [List.mem_map, List.mem_range] at hr
        rcases hr with ⟨iv, hiv, rfl⟩
        rw [dif_pos hiv]
        exact (pd.val.2.2 ⟨iv, hiv⟩).isLt
      · intro y hy
        simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hy
        rcases hy with ⟨iv, hiv, _, _, rfl⟩
        rw [dif_pos hiv]
        exact Fin.isLt _
      · intro y hy
        simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hy
        rcases hy with ⟨iv, hiv, _, _, rfl⟩
        rw [dif_pos hiv]
        exact Fin.isLt _
    · intro i
      dsimp only
      rw [getD_eq_getElem _ 0 i.val (by simp [i.isLt])]
      simp [i.isLt]
  clear hsymActOf_def
  have hsymPair_valid : ∀ {n : ℕ} (pd : PosData n),
      (symPosOf pd, symActOf pd) ∈ validSymLabels ctx ∧
      (fixedIdxs (symPosOf pd) (symActOf pd)).length ≤ ctxBRed ctx ∧
      (∀ i : Fin pd.val.1, (symActOf pd).1.getD i.val 0 = (pd.val.2.2 i).val) ∧
      ∀ i : Fin pd.val.1,
        treeNodeOf hB ht0 hlive0 (pd.val.2.1 i) =
          treeNodeOf hB ht0 hlive0 (pd.val.2.1 ⟨0, pd.property.1⟩) := by
    intro n pd
    obtain ⟨hk1, hkB, hlen_b, hinj_b, hlive_b, hconn_b, hr_idem, hr_card, hr_st, hr_vw, _⟩ := pd.property
    obtain ⟨hpos_in, hpos_k, heq1_pos, heq2_pos, hst_pos⟩ := hsymPos_access pd
    obtain ⟨hact_in, hr_getD, ho1_act, ho2_act⟩ := hsymAct_access pd
    have hsame_node : ∀ i : Fin pd.val.1,
        treeNodeOf hB ht0 hlive0 (pd.val.2.1 i) = treeNodeOf hB ht0 hlive0 (pd.val.2.1 ⟨0, hk1⟩) := by
      intro i
      have hp := hconn_b ⟨0, hk1⟩ i
      induction hp with
      | refl => rfl
      | @tail x y _ hadj ih =>
        have hsx := treeNodeOf_spec hB ht0 hlive0 (hlive_b x)
        have hsy := treeNodeOf_spec hB ht0 hlive0 (hlive_b y)
        have heq_xy : treeNodeOf hB ht0 hlive0 (pd.val.2.1 y) = treeNodeOf hB ht0 hlive0 (pd.val.2.1 x) :=
          uncomp_nodes_eq_of_view ht0 hinit_live hsy.1 hsx.1
            (hsy.2.1.trans ((hlen_b y).trans ((hlen_b x).symm.trans hsx.2.1.symm)))
            hsy.2.2 hsx.2.2 (hadj.elim (fun h1 => Or.inl h1.symm) (fun h2 => Or.inr h2.symm))
        exact heq_xy.trans ih
    have hfix_len : (fixedIdxs (symPosOf pd) (symActOf pd)).length ≤ ctxBRed ctx := by
      have hfix_sub : (fixedIdxs (symPosOf pd) (symActOf pd)).toFinset ⊆
          (Finset.univ.filter (fun i : Fin pd.val.1 => pd.val.2.2 i = i)).image Fin.val := by
        intro iv hiv
        have hiv' : iv ∈ fixedIdxs (symPosOf pd) (symActOf pd) := List.mem_toFinset.mp hiv
        simp only [fixedIdxs, hpos_k, List.mem_filter, List.mem_range, decide_eq_true_eq] at hiv'
        let i : Fin pd.val.1 := ⟨iv, hiv'.1⟩
        have hri : pd.val.2.2 i = i := Fin.ext (by rw [← hr_getD i]; exact hiv'.2)
        exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hri⟩, rfl⟩
      have hnd_fix : (fixedIdxs (symPosOf pd) (symActOf pd)).Nodup :=
        List.Nodup.filter _ List.nodup_range
      calc
        (fixedIdxs (symPosOf pd) (symActOf pd)).length
          = (fixedIdxs (symPosOf pd) (symActOf pd)).toFinset.card :=
            (List.toFinset_card_of_nodup hnd_fix).symm
        _ ≤ ((Finset.univ.filter (fun i : Fin pd.val.1 => pd.val.2.2 i = i)).image Fin.val).card :=
            Finset.card_le_card hfix_sub
        _ ≤ (Finset.univ.filter (fun i : Fin pd.val.1 => pd.val.2.2 i = i)).card := Finset.card_image_le
        _ ≤ ctxBRed ctx := hr_card
    have hctxI : ctxI ctx = I := rfl
    have hctxD : ctxD ctx = D := rfl
    refine ⟨?_, hfix_len, hr_getD, hsame_node⟩
    rw [mem_validSymLabels_iff]
    refine ⟨hpos_in, hact_in, ?_⟩
    unfold actValid
    rw [decide_eq_true_eq]
    dsimp only
    refine ⟨?_, hfix_len, ?_, ?_, ?_⟩
    · intro iv hiv
      rw [hpos_k] at hiv
      let i : Fin pd.val.1 := ⟨iv, hiv⟩
      change (symActOf pd).1.getD ((symActOf pd).1.getD i.val 0) 0 = (symActOf pd).1.getD i.val 0
      rw [hr_getD i, hr_getD (pd.val.2.2 i), hr_idem i]
    · intro iv hiv
      rw [hpos_k] at hiv
      let i : Fin pd.val.1 := ⟨iv, hiv⟩
      change stateAt (symPosOf pd) ((symActOf pd).1.getD i.val 0) = stateAt (symPosOf pd) i.val
      rw [hr_getD i, hst_pos (pd.val.2.2 i), hst_pos i, hr_st i]
    · intro iv hiv jv hjv
      rw [hpos_k] at hiv hjv
      let i : Fin pd.val.1 := ⟨iv, hiv⟩
      let j : Fin pd.val.1 := ⟨jv, hjv⟩
      change (eq1At (symPosOf pd) i.val j.val = true →
          eq1At (symPosOf pd) ((symActOf pd).1.getD i.val 0) ((symActOf pd).1.getD j.val 0) = true) ∧
        (eq2At (symPosOf pd) i.val j.val = true →
          eq2At (symPosOf pd) ((symActOf pd).1.getD i.val 0) ((symActOf pd).1.getD j.val 0) = true)
      rw [hr_getD i, hr_getD j, heq1_pos i j, heq1_pos (pd.val.2.2 i) (pd.val.2.2 j),
        heq2_pos i j, heq2_pos (pd.val.2.2 i) (pd.val.2.2 j)]
      simp only [decide_eq_true_eq]
      exact ⟨hr_vw i j .one, hr_vw i j .two⟩
    · intro iv hiv jv hjv wi hwi wj hwj
      have hiv_lt : iv < pd.val.1 := hpos_k ▸ List.mem_range.mp (List.mem_filter.mp hiv).1
      have hjv_lt : jv < pd.val.1 := hpos_k ▸ List.mem_range.mp (List.mem_filter.mp hjv).1
      let i : Fin pd.val.1 := ⟨iv, hiv_lt⟩
      let j : Fin pd.val.1 := ⟨jv, hjv_lt⟩
      have hlen_ij : (blockConcat (pd.val.2.1 i)).length = (blockConcat (pd.val.2.1 j)).length := by
        rw [blockConcat_length, blockConcat_length, hlen_b i, hlen_b j]
      have hext_eq : extEqNat I (symPosOf pd) i.val (words.getD wi []) j.val (words.getD wj []) =
          (decide (view1 (blockConcat (pd.val.2.1 i) ++ decHist I (words.getD wi [])) =
            view1 (blockConcat (pd.val.2.1 j) ++ decHist I (words.getD wj []))),
           decide (view2 (blockConcat (pd.val.2.1 i) ++ decHist I (words.getD wi [])) =
            view2 (blockConcat (pd.val.2.1 j) ++ decHist I (words.getD wj [])))) := by
        unfold extEqNat
        rw [heq1_pos i j, heq2_pos i j]
        exact extEqFrom_exact I hlen_ij _ _
      rw [hctxI, hctxD] at hwi hwj ⊢
      have hwi' : wi < NW := hwi
      have hwj' : wj < NW := hwj
      change ((extEqNat I (symPosOf pd) i.val (words.getD wi []) j.val (words.getD wj [])).1 = true →
          (symActOf pd).2.1.getD (i.val * NW + wi) 0 = (symActOf pd).2.1.getD (j.val * NW + wj) 0) ∧
        ((extEqNat I (symPosOf pd) i.val (words.getD wi []) j.val (words.getD wj [])).2 = true →
          (symActOf pd).2.2.getD (i.val * NW + wi) 0 = (symActOf pd).2.2.getD (j.val * NW + wj) 0)
      rw [hext_eq, ho1_act i wi hwi', ho1_act j wj hwj', ho2_act i wi hwi', ho2_act j wj hwj']
      simp only [decide_eq_true_eq]
      exact ⟨fun hv1 => by rw [hv1], fun hv2 => by rw [hv2]⟩
  -- Exact correspondence of `symNextState` with `(t0.label a0).qLam B` on `pd`
  have hsymNext_eq_treeState : ∀ {n : ℕ} (pd : PosData n) (i : Fin pd.val.1)
      (u : Fin D → Signal I.X1 I.X2),
      let next_q := symNextState E ctx (symPosOf pd) (symActOf pd) i.val (encBlock I u)
      ((res.2.getD next_q false = true) ↔ liveBlk (pd.val.2.1 i ++ [u])) ∧
      (liveBlk (pd.val.2.1 i ++ [u]) →
        next_q = (treeState hB ht0 hlive0 (pd.val.2.1 i ++ [u])).val) := by
    intro n pd i u
    let a0 := treeNodeOf hB ht0 hlive0 (pd.val.2.1 ⟨0, pd.property.1⟩)
    have ha0_eq : treeNodeOf hB ht0 hlive0 (pd.val.2.1 i) = a0 := (hsymPair_valid pd).2.2.2 i
    obtain ⟨_, _, _, _, hlive_b, _⟩ := pd.property
    obtain ⟨_, _, _, _, hst_pos⟩ := hsymPos_access pd
    obtain ⟨_, _, ho1_act, ho2_act⟩ := hsymAct_access pd
    let blkTyped : Fin D → Signal I.X1 I.X2 × (I.Y1 × I.Y2) :=
      fun t => (u t, (t0.label a0).out (blockConcat (pd.val.2.1 i)) ((List.ofFn u).take (t.val + 1)))
    have hctxI : ctxI ctx = I := rfl
    have hctxD : ctxD ctx = D := rfl
    have hctxB : ctxBCode ctx = res.1 := rfl
    have hnext_q_eq : symNextState E ctx (symPosOf pd) (symActOf pd) i.val (encBlock I u) =
        ((t0.label a0).qLam B (blockConcat (pd.val.2.1 i)) u).val := by
      unfold symNextState NodeLabel.qLam
      rw [hctxI, hctxD, hctxB]
      have hst_eq : stateAt (symPosOf pd) i.val =
          ((t0.label a0).state B.init (blockConcat (pd.val.2.1 i))).val := by
        rw [hst_pos i]
        unfold treeState
        rw [ha0_eq]
      rw [hst_eq, hB_step, E.encIOBlock_compat I D blkTyped]
      dsimp only
      have hio_eq : ((List.range D).map fun t =>
          let s := (encBlock I u).getD t 0
          let wi := cIdxOf words ((encBlock I u).take (t + 1))
          (decSigX1 I s, decSigX2 I s, decSigG s,
            (symActOf pd).2.1.getD (i.val * NW + wi) 0,
            (symActOf pd).2.2.getD (i.val * NW + wi) 0)) =
          ((List.ofFn blkTyped).map fun s => (s.1.1.val, s.1.2.1.val, s.1.2.2.idx, s.2.1.val, s.2.2.val)) := by
        apply List.ext_getElem
        · rw [List.length_map, List.length_range, List.length_map, List.length_ofFn]
        · intro t ht1 ht2
          have ht_lt : t < D := by rw [List.length_map, List.length_range] at ht1; exact ht1
          let tf : Fin D := ⟨t, ht_lt⟩
          simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
          have hs_eq : (encBlock I u).getD t 0 = encSigTyped I (u tf) := by
            have hlen_eb : (encBlock I u).length = D := by
              rw [encBlock, encHist, List.length_map, List.length_ofFn]
            rw [getD_eq_getElem _ 0 t (by omega)]
            simp only [encBlock, encHist, List.getElem_map, List.getElem_ofFn]
            rfl
          obtain ⟨hx1, hx2, hg, _⟩ := decSigFields_encSigTyped I (u tf)
          have htake_eq : (encBlock I u).take (t + 1) = encHist I ((List.ofFn u).take (t + 1)) := by
            unfold encBlock encHist
            rw [List.map_take]
          have hmem_words : encHist I ((List.ofFn u).take (t + 1)) ∈ words := by
            have hlen_tk : (encHist I ((List.ofFn u).take (t + 1))).length = t + 1 := by
              rw [encHist, List.length_map, List.length_take, List.length_ofFn]
              omega
            rw [mem_nonemptyExtWords_iff]
            refine ⟨by omega, by omega, ?_⟩
            intro x hx
            obtain ⟨s0, _, rfl⟩ := List.mem_map.mp hx
            exact encSigTyped_lt I s0
          obtain ⟨hwi_lt, hwi_get⟩ := cIdxOf_lt_and_getElem hmem_words
          let wi := cIdxOf words ((encBlock I u).take (t + 1))
          have hwi_lt' : wi < NW := by dsimp [wi]; rwa [htake_eq]
          have hwords_wi : words.getD wi [] = encHist I ((List.ofFn u).take (t + 1)) := by
            rw [getD_eq_getElem words [] wi hwi_lt']
            dsimp [wi]; simpa [htake_eq] using hwi_get
          have ho1_eq : (symActOf pd).2.1.getD (i.val * NW + wi) 0 = (blkTyped tf).2.1.val := by
            dsimp only [blkTyped, NodeLabel.out]
            rw [ho1_act i wi hwi_lt', hwords_wi, decHist_encHist]
          have ho2_eq : (symActOf pd).2.2.getD (i.val * NW + wi) 0 = (blkTyped tf).2.2.val := by
            dsimp only [blkTyped, NodeLabel.out]
            rw [ho2_act i wi hwi_lt', hwords_wi, decHist_encHist]
          rw [hs_eq, hx1, hx2, hg, ho1_eq, ho2_eq]
      rw [hio_eq]
    obtain ⟨hv_a0_i, _, hmem_bi⟩ := treeNodeOf_spec hB ht0 hlive0 (hlive_b i)
    rw [ha0_eq] at hv_a0_i hmem_bi
    rcases hmem_bi with ⟨s_bi, hs_bi⟩
    obtain ⟨hreach_bi, _, hst_bi⟩ := uncomp_node_inv ht0 hinit_live a0 hv_a0_i _ s_bi hs_bi
    have hreach_next : ReachableInB B (a0.length + 1) (blockConcat (pd.val.2.1 i) ++ List.ofFn u)
        ((t0.label a0).qLam B (blockConcat (pd.val.2.1 i)) u) := by
      have hst_bi' : (t0.label a0).state B.init (blockConcat (pd.val.2.1 i)) = s_bi := hst_bi
      have hstep := reachableInB_step (B := B) hreach_bi u
        (fun j => (t0.label a0).out (blockConcat (pd.val.2.1 i)) ((List.ofFn u).take (j.val + 1)))
      unfold NodeLabel.qLam
      rw [hst_bi']
      exact hstep
    have hlive_iff := reachableInB_live hB hreach_next
    dsimp only
    rw [hnext_q_eq]
    refine ⟨?_, fun hl_next => ?_⟩
    · rw [← hQlive_mem ((t0.label a0).qLam B (blockConcat (pd.val.2.1 i)) u), hlive_iff]
      unfold liveBlk
      rw [blockConcat_append_singleton]
    · obtain ⟨_, _, _, hst_next⟩ := treeNodeOf_append_singleton hB ht0 hlive0 hl_next
      rw [hst_next, ha0_eq]
  -- Root `PosData 0`
  have hpd0_ex : ∃ pd0 : PosData 0, symPosOf pd0 = initSymPos := by
    let blocks0 : Fin 1 → List (Fin D → Signal I.X1 I.X2) := fun _ => []
    let rFn0 : Fin 1 → Fin 1 := id
    have hcard0 : (Finset.univ.filter (fun i : Fin 1 => rFn0 i = i)).card ≤ ctxBRed ctx := by
      have hc1 : (Finset.univ.filter (fun i : Fin 1 => rFn0 i = i)).card ≤ 1 :=
        le_trans (Finset.card_le_univ _) (by simp)
      have hpos := ctxBRed_pos ctx
      omega
    let pd0 : PosData 0 :=
      ⟨⟨1, blocks0, rFn0⟩, le_refl 1, ctxBFull_pos ctx, (fun _ => rfl),
        (fun i j _ => Subsingleton.elim i j), (fun _ => hlive0),
        (fun i j => by rw [Subsingleton.elim i j]), (fun _ => rfl), hcard0,
        (fun _ => rfl), (fun _ _ _ h => h), (fun m hm => by omega)⟩
    refine ⟨pd0, ?_⟩
    have hst0 : (treeState hB ht0 hlive0 []).val = 0 := by
      obtain ⟨hv0, hl0, hm0⟩ := treeNodeOf_spec hB ht0 hlive0 (ws := []) hlive0
      have ha_nil : treeNodeOf hB ht0 hlive0 ([] : List (Fin D → Signal I.X1 I.X2)) = [] :=
        List.eq_nil_of_length_eq_zero hl0
      rcases hm0 with ⟨s0, hs0⟩
      rw [ha_nil] at hv0 hs0
      have hst_eq := (uncomp_node_inv ht0 hinit_live [] hv0 [] s0 hs0).2.2
      have hs0_init : s0 = B.init := ht0.2.1 [] s0 hs0
      unfold treeState
      rw [ha_nil, blockConcat_nil, hst_eq, hs0_init]
      exact hB_init
    rw [hsymPosOf_def pd0]
    simp [initSymPos, pd0, blocks0, List.finRange_succ, List.finRange_zero, hst0]
  exact ⟨symPosOf, symActOf, hsymPosOf_def, hsymPos_access, hsymPair_valid,
    hsymNext_eq_treeState, hpd0_ex⟩

lemma exists_uncomp_pos_system (E : Thm34Engine)
    (c : DPACode) (I : Instance) (D_m1 D : ℕ) (hD_def : D = D_m1 + 1)
    (φ : Formula ℕ ℕ ℕ ℕ)
    (hCons : ∀ g ∈ Pref c.lang, ConsensusSolvableWithin Bool (leftQuot g c.lang) D)
    (res : GenDPACode × List Bool)
    (ctx : SymCtx) (hctx_def : ctx = (I, D_m1, res.1, res.2))
    (B : DPA (Fin (res.1.1 + 1)) (Fin D → Signal I.X1 I.X2 × (I.Y1 × I.Y2)))
    (Qlive : Set (Fin (res.1.1 + 1)))
    (hB_init : B.init.val = 0)
    (hB_step : ∀ (q : Fin (res.1.1 + 1)) (blk : Fin D → Signal I.X1 I.X2 × (I.Y1 × I.Y2)),
      (B.step q blk).val =
        (res.1.2.1.getD (q.val * (E.blockAlphaMinusOne I D + 1) +
          (E.encIOBlockTyped I D blk).val) 0) % (res.1.1 + 1))
    (hQlive_mem : ∀ q : Fin (res.1.1 + 1), q ∈ Qlive ↔ res.2.getD q.val false = true)
    (hB : IsBlockAutomaton c.lang (instFormulaOf I φ) D B Qlive)
    (hlive0 : ([] : List CommGraph) ∈ Pref c.lang)
    (t0 : LabeledTree (NodeLabel I.X1 I.X2 I.Y1 I.Y2 (Fin (res.1.1 + 1))))
    (ht0 : IsUncompressedComponentTree B Qlive t0)
    (liveBlk : List (Fin D → Signal I.X1 I.X2) → Prop)
    (hliveBlk_def : liveBlk = fun ws => graphOfHist (blockConcat ws) ∈ Pref c.lang)
    {K_prio : ℕ}
    (rkFn : List (Fin D → Signal I.X1 I.X2) → Lex (Fin (K_prio + 1) → Ordinal.{0})) :
    ∃ (symPosOf : ∀ {n : ℕ},
        UncompPosData I D (ctxBFull ctx) (ctxBRed ctx) liveBlk (treeState hB ht0 hlive0) rkFn n → SymPosCode)
      (symActOf : ∀ {n : ℕ},
        UncompPosData I D (ctxBFull ctx) (ctxBRed ctx) liveBlk (treeState hB ht0 hlive0) rkFn n → SymActCode)
      (pd0 : UncompPosData I D (ctxBFull ctx) (ctxBRed ctx) liveBlk (treeState hB ht0 hlive0) rkFn 0),
      symPosOf pd0 = initSymPos ∧
      (∀ {n : ℕ} (pd : UncompPosData I D (ctxBFull ctx) (ctxBRed ctx) liveBlk (treeState hB ht0 hlive0) rkFn n),
        (symPosOf pd, symActOf pd) ∈ validSymLabels ctx ∧
        (symPosOf pd).1 = pd.val.1 ∧
        (∀ i : Fin pd.val.1, (symActOf pd).1.getD i.val 0 = (pd.val.2.2 i).val)) ∧
      (∀ {n : ℕ} (pd : UncompPosData I D (ctxBFull ctx) (ctxBRed ctx) liveBlk (treeState hB ht0 hlive0) rkFn n)
        (d : ℕ) (hd : d < (symComponents E ctx (symPosOf pd) (symActOf pd)).length),
        ∃ pd' : UncompPosData I D (ctxBFull ctx) (ctxBRed ctx) liveBlk (treeState hB ht0 hlive0) rkFn (n + 1),
          symPosOf pd' = childSymPos I (symPosOf pd)
            ((symComponents E ctx (symPosOf pd) (symActOf pd))[d]'hd) ∧
          pd'.val.1 = ((symComponents E ctx (symPosOf pd) (symActOf pd))[d]'hd).length ∧
          ∀ j : Fin pd'.val.1,
            let ej := ((symComponents E ctx (symPosOf pd) (symActOf pd))[d]'hd).getD j.val inhSymExt
            ∃ (ir : Fin pd.val.1) (u : Fin D → Signal I.X1 I.X2),
              ej.1 = ir.val ∧ u = decBlock I D ej.2.1 ∧
              pd'.val.2.1 j = pd.val.2.1 ir ++ [u] ∧
              ej.2.2 = (treeState hB ht0 hlive0 (pd'.val.2.1 j)).val) := by
  classical
  have hmaps := exists_uncomp_sym_maps E c I D_m1 D hD_def φ res ctx hctx_def B Qlive
    hB_init hB_step hQlive_mem hB hlive0 t0 ht0 liveBlk hliveBlk_def rkFn
  subst hD_def
  subst hctx_def
  subst hliveBlk_def
  let D := D_m1 + 1
  have hD : 1 ≤ D := Nat.succ_pos D_m1
  let ctx : SymCtx := (I, D_m1, res.1, res.2)
  let liveBlk : List (Fin D → Signal I.X1 I.X2) → Prop :=
    fun ws => graphOfHist (blockConcat ws) ∈ Pref c.lang
  obtain ⟨symPosOf, symActOf, hsymPosOf_def, hsymPos_access, hsymPair_valid,
    hsymNext_eq_treeState, ⟨pd0, hpd0_pos⟩⟩ := hmaps
  have hBRed_eq : (1 + (res.1.1 + 1)) ^ (sigCard I ^ D) * (sigCard I ^ D) = ctxBRed ctx := by
    simp [ctxBRed, ctxBlockCard, ctxQBCard, ctxBCode, ctxI, ctxD, ctx, D, myPow_eq]
  refine ⟨symPosOf, symActOf, pd0, hpd0_pos,
    fun pd => ⟨(hsymPair_valid pd).1, (hsymPos_access pd).2.1, (hsymPair_valid pd).2.2.1⟩, ?_⟩
  intro n pd d hd
  have hlen_b : ∀ i : Fin pd.val.1, (pd.val.2.1 i).length = n := pd.property.2.2.1
  have hinj_b : Function.Injective pd.val.2.1 := pd.property.2.2.2.1
  have hpa_acc := hsymPos_access pd
  rcases hpa_acc with ⟨_, hpos_k, heq1_pos, heq2_pos, _⟩
  have hfix_le := (hsymPair_valid pd).2.1
  have hctxI : ctxI ctx = I := rfl
  have hctxD : ctxD ctx = D := rfl
  let blkOfElem : SymExtElem → List (Fin D → Signal I.X1 I.X2) := fun e =>
    if h : e.1 < pd.val.1 then pd.val.2.1 ⟨e.1, h⟩ ++ [decBlock I D e.2.1] else []
  have hblkOfElem_pos : ∀ (e : SymExtElem) (h : e.1 < pd.val.1),
      blkOfElem e = pd.val.2.1 ⟨e.1, h⟩ ++ [decBlock I D e.2.1] := fun _ h => dif_pos h
  have helem_props : ∀ e ∈ symLiveExts E ctx (symPosOf pd) (symActOf pd),
      e.1 < pd.val.1 ∧ (e.2.1.length = D ∧ ∀ x ∈ e.2.1, x < sigCard I) ∧
      e.2.1 = encBlock I (decBlock I D e.2.1) ∧
      liveBlk (blkOfElem e) ∧
      e.2.2 = (treeState hB ht0 hlive0 (blkOfElem e)).val := by
    intro e he
    have hm_ext := (mem_symLiveExts_iff E ctx (symPosOf pd) (symActOf pd) e).mp he
    rcases hm_ext with ⟨he_fix, he_blk, he_q, he_live⟩
    rw [hctxI, hctxD] at he_blk
    have he1_lt : e.1 < pd.val.1 := by
      have := List.mem_range.mp (List.mem_filter.mp he_fix).1
      omega
    have hm_blk := (mem_fullBlocks_iff I D e.2.1).mp he_blk
    rcases hm_blk with ⟨hu_len, hu_lt⟩
    have henc_dec : e.2.1 = encBlock I (decBlock I D e.2.1) := by
      unfold encBlock
      rw [ofFn_decBlock I hu_len, encHist_decHist I hu_lt]
    let ir : Fin pd.val.1 := ⟨e.1, he1_lt⟩
    let u := decBlock I D e.2.1
    have hblk_eq : blkOfElem e = pd.val.2.1 ir ++ [u] := hblkOfElem_pos e he1_lt
    have hsn := hsymNext_eq_treeState pd ir u
    have hq_eq : e.2.2 = symNextState E ctx (symPosOf pd) (symActOf pd) ir.val (encBlock I u) := by
      rw [he_q, ← henc_dec]
    have hlive_ext : liveBlk (pd.val.2.1 ir ++ [u]) := by
      apply hsn.1.mp
      dsimp only [ctxLive, ctx] at he_live
      rwa [← hq_eq]
    rw [hblk_eq]
    exact ⟨he1_lt, ⟨hu_len, hu_lt⟩, henc_dec, hlive_ext, hq_eq.trans (hsn.2 hlive_ext)⟩
  have hadj_exact : ∀ (ea eb : SymExtElem),
      ea ∈ symLiveExts E ctx (symPosOf pd) (symActOf pd) →
      eb ∈ symLiveExts E ctx (symPosOf pd) (symActOf pd) →
      extEqNat I (symPosOf pd) ea.1 ea.2.1 eb.1 eb.2.1 =
        (decide (view1 (blockConcat (blkOfElem ea)) = view1 (blockConcat (blkOfElem eb))),
         decide (view2 (blockConcat (blkOfElem ea)) = view2 (blockConcat (blkOfElem eb)))) := by
    intro ea eb ha hb
    have hsa := helem_props ea ha
    have hsb := helem_props eb hb
    let ia : Fin pd.val.1 := ⟨ea.1, hsa.1⟩
    let ib : Fin pd.val.1 := ⟨eb.1, hsb.1⟩
    have hlen_ab : (blockConcat (pd.val.2.1 ia)).length = (blockConcat (pd.val.2.1 ib)).length := by
      rw [blockConcat_length, blockConcat_length, hlen_b ia, hlen_b ib]
    rw [hblkOfElem_pos ea hsa.1, hblkOfElem_pos eb hsb.1]
    unfold extEqNat
    rw [heq1_pos ia ib, heq2_pos ia ib, extEqFrom_exact I hlen_ab,
      blockConcat_append_singleton, blockConcat_append_singleton,
      ofFn_decBlock I hsa.2.1.1, ofFn_decBlock I hsb.2.1.1]
  have hsym_S : ∀ a ∈ symLiveExts E ctx (symPosOf pd) (symActOf pd),
      ∀ b ∈ symLiveExts E ctx (symPosOf pd) (symActOf pd),
      symExtAdj (ctxI ctx) (symPosOf pd) a b = symExtAdj (ctxI ctx) (symPosOf pd) b a := by
    intro a ha b hb
    rw [hctxI]
    unfold symExtAdj
    rw [hadj_exact a b ha hb, hadj_exact b a hb ha]
    simp only [orBool_eq]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨fun h => h.elim (fun h1 => Or.inl h1.symm) (fun h2 => Or.inr h2.symm),
      fun h => h.elim (fun h1 => Or.inl h1.symm) (fun h2 => Or.inr h2.symm)⟩
  have hfor_comp : ∀ (comp : List SymExtElem),
      1 ≤ comp.length → comp.length ≤ ctxBFull ctx → comp.Nodup →
      (∀ e ∈ comp, e ∈ symLiveExts E ctx (symPosOf pd) (symActOf pd)) →
      ((∀ a ∈ symLiveExts E ctx (symPosOf pd) (symActOf pd),
          ∀ b ∈ symLiveExts E ctx (symPosOf pd) (symActOf pd),
            symExtAdj (ctxI ctx) (symPosOf pd) a b = symExtAdj (ctxI ctx) (symPosOf pd) b a) →
        ∀ j1 j2 : Fin comp.length,
          Relation.ReflTransGen
            (fun x y : Fin comp.length =>
              symExtAdj (ctxI ctx) (symPosOf pd) comp[x] comp[y] = true) j1 j2) →
      ∃ pd' : UncompPosData I D (ctxBFull ctx) (ctxBRed ctx) liveBlk (treeState hB ht0 hlive0) rkFn (n + 1),
        symPosOf pd' = childSymPos I (symPosOf pd) comp ∧
        pd'.val.1 = comp.length ∧
        ∀ j : Fin pd'.val.1,
          let ej := comp.getD j.val inhSymExt
          ∃ (ir : Fin pd.val.1) (u : Fin D → Signal I.X1 I.X2),
            ej.1 = ir.val ∧ u = decBlock I D ej.2.1 ∧
            pd'.val.2.1 j = pd.val.2.1 ir ++ [u] ∧
            ej.2.2 = (treeState hB ht0 hlive0 (pd'.val.2.1 j)).val := by
    intro comp hk'1 hk'B hcomp_nd hcomp_in_S hcomp_conn
    let blocks' : Fin comp.length → List (Fin D → Signal I.X1 I.X2) :=
      fun j => blkOfElem (comp[j.val]'j.isLt)
    have hlen' : ∀ j : Fin comp.length, (blocks' j).length = n + 1 := by
      intro j
      have hs := helem_props (comp[j.val]'j.isLt) (hcomp_in_S _ (List.getElem_mem j.isLt))
      dsimp only [blocks']
      rw [hblkOfElem_pos _ hs.1, List.length_append, hlen_b, List.length_singleton]
    have hinj' : Function.Injective blocks' := by
      intro j1 j2 heq
      have hs1 := helem_props (comp[j1.val]'j1.isLt) (hcomp_in_S _ (List.getElem_mem j1.isLt))
      have hs2 := helem_props (comp[j2.val]'j2.isLt) (hcomp_in_S _ (List.getElem_mem j2.isLt))
      dsimp only [blocks'] at heq
      rw [hblkOfElem_pos _ hs1.1, hblkOfElem_pos _ hs2.1] at heq
      have hlen12 : (pd.val.2.1 ⟨(comp[j1.val]'j1.isLt).1, hs1.1⟩).length =
          (pd.val.2.1 ⟨(comp[j2.val]'j2.isLt).1, hs2.1⟩).length := by
        rw [hlen_b, hlen_b]
      obtain ⟨hb_eq, hu_eq⟩ := List.append_inj heq hlen12
      have hi_eq : (comp[j1.val]'j1.isLt).1 = (comp[j2.val]'j2.isLt).1 :=
        congrArg Fin.val (hinj_b hb_eq)
      have hu_singleton := List.cons.inj hu_eq |>.1
      have huNat_eq : (comp[j1.val]'j1.isLt).2.1 = (comp[j2.val]'j2.isLt).2.1 := by
        rw [hs1.2.2.1, hs2.2.2.1, hu_singleton]
      have hm1 := (mem_symLiveExts_iff E ctx (symPosOf pd) (symActOf pd) _).mp
        (hcomp_in_S _ (List.getElem_mem j1.isLt))
      have hm2 := (mem_symLiveExts_iff E ctx (symPosOf pd) (symActOf pd) _).mp
        (hcomp_in_S _ (List.getElem_mem j2.isLt))
      have hq_eq12 : (comp[j1.val]'j1.isLt).2.2 = (comp[j2.val]'j2.isLt).2.2 := by
        rw [hm1.2.2.1, hm2.2.2.1, hi_eq, huNat_eq]
      have he_eq : comp[j1.val]'j1.isLt = comp[j2.val]'j2.isLt :=
        Prod.ext hi_eq (Prod.ext huNat_eq hq_eq12)
      exact Fin.ext ((List.Nodup.getElem_inj_iff hcomp_nd).mp he_eq)
    have hlive' : ∀ j : Fin comp.length, liveBlk (blocks' j) :=
      fun j => (helem_props _ (hcomp_in_S _ (List.getElem_mem j.isLt))).2.2.2.1
    have hconn' : ∀ j1 j2 : Fin comp.length, Relation.ReflTransGen
        (fun x y : Fin comp.length => EdgeAdj (blockConcat (blocks' x)) (blockConcat (blocks' y))) j1 j2 := by
      intro j1 j2
      have hr := hcomp_conn hsym_S j1 j2
      induction hr with
      | refl => exact .refl
      | @tail x y _ hxy ih =>
        have hx_S := hcomp_in_S (comp[x.val]'x.isLt) (List.getElem_mem x.isLt)
        have hy_S := hcomp_in_S (comp[y.val]'y.isLt) (List.getElem_mem y.isLt)
        rw [hctxI] at hxy
        change symExtAdj I (symPosOf pd) (comp[x.val]'x.isLt) (comp[y.val]'y.isLt) = true at hxy
        unfold symExtAdj at hxy
        rw [hadj_exact (comp[x.val]'x.isLt) (comp[y.val]'y.isLt) hx_S hy_S] at hxy
        simp only [orBool_eq, Bool.or_eq_true, decide_eq_true_eq] at hxy
        exact ih.tail hxy
    have hex_rFn := uncomp_mk_child_rFn c I D hD hCons (treeState hB ht0 hlive0) rkFn
      (ctxBRed ctx) hBRed_eq n comp.length hk'1 blocks' hlen' hinj' hlive' hconn'
    rcases hex_rFn with ⟨rFn', hr1, hr2, hr3, hr4, hr5⟩
    let pd' : UncompPosData I D (ctxBFull ctx) (ctxBRed ctx) liveBlk (treeState hB ht0 hlive0) rkFn (n + 1) :=
      ⟨⟨comp.length, blocks', rFn'⟩, hk'1, hk'B, hlen', hinj', hlive', hconn', hr1, hr2, hr3, hr4, hr5⟩
    refine ⟨pd', ?_, rfl, ?_⟩
    · rw [hsymPosOf_def pd']
      dsimp only [childSymPos, pd', blocks']
      refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
      · apply List.flatMap_congr
        intro a ha
        have ha_lt : a < comp.length := List.mem_range.mp ha
        apply List.map_congr_left
        intro b hb
        have hb_lt : b < comp.length := List.mem_range.mp hb
        have hite1 : (if h : a < comp.length ∧ b < comp.length then
            decide (view1 (blockConcat (blkOfElem (comp[a]'h.1))) =
              view1 (blockConcat (blkOfElem (comp[b]'h.2))))
          else false) =
          decide (view1 (blockConcat (blkOfElem (comp[a]'ha_lt))) =
            view1 (blockConcat (blkOfElem (comp[b]'hb_lt)))) := dif_pos ⟨ha_lt, hb_lt⟩
        rw [hite1, getD_eq_getElem _ inhSymExt a ha_lt,
          getD_eq_getElem _ inhSymExt b hb_lt,
          hadj_exact (comp[a]'ha_lt) (comp[b]'hb_lt) (hcomp_in_S _ (List.getElem_mem ha_lt))
            (hcomp_in_S _ (List.getElem_mem hb_lt))]
      · apply List.flatMap_congr
        intro a ha
        have ha_lt : a < comp.length := List.mem_range.mp ha
        apply List.map_congr_left
        intro b hb
        have hb_lt : b < comp.length := List.mem_range.mp hb
        have hite2 : (if h : a < comp.length ∧ b < comp.length then
            decide (view2 (blockConcat (blkOfElem (comp[a]'h.1))) =
              view2 (blockConcat (blkOfElem (comp[b]'h.2))))
          else false) =
          decide (view2 (blockConcat (blkOfElem (comp[a]'ha_lt))) =
            view2 (blockConcat (blkOfElem (comp[b]'hb_lt)))) := dif_pos ⟨ha_lt, hb_lt⟩
        rw [hite2, getD_eq_getElem _ inhSymExt a ha_lt,
          getD_eq_getElem _ inhSymExt b hb_lt,
          hadj_exact (comp[a]'ha_lt) (comp[b]'hb_lt) (hcomp_in_S _ (List.getElem_mem ha_lt))
            (hcomp_in_S _ (List.getElem_mem hb_lt))]
      · apply List.ext_getElem (by simp)
        intro j hj1 hj2
        have hj_lt : j < comp.length := by simpa using hj2
        simp only [List.getElem_map, List.getElem_finRange]
        exact ((helem_props (comp[j]'hj_lt) (hcomp_in_S _ (List.getElem_mem hj_lt))).2.2.2.2).symm
    · intro j
      have hj_lt : j.val < comp.length := j.isLt
      dsimp only
      rw [getD_eq_getElem _ inhSymExt j.val hj_lt]
      have hj_S := hcomp_in_S (comp[j.val]'hj_lt) (List.getElem_mem hj_lt)
      have hep_j := helem_props (comp[j.val]'hj_lt) hj_S
      rcases hep_j with ⟨he1_lt, _, _, _, hq_st⟩
      have hpd'_blk : pd'.val.2.1 j = blkOfElem (comp[j.val]'hj_lt) := rfl
      rw [hpd'_blk]
      exact ⟨⟨(comp[j.val]'hj_lt).1, he1_lt⟩, decBlock I D (comp[j.val]'hj_lt).2.1,
        rfl, rfl, hblkOfElem_pos _ he1_lt, hq_st⟩
  have hcomp_all := (symComponents_props E ctx (symPosOf pd) (symActOf pd) hfix_le).2 d hd
  exact hfor_comp ((symComponents E ctx (symPosOf pd) (symActOf pd))[d]'hd)
    hcomp_all.1 hcomp_all.2.1 hcomp_all.2.2.1 hcomp_all.2.2.2.1 hcomp_all.2.2.2.2

/-- Completeness of the compressed symbolic tree game: if an accepting uncompressed
component tree exists (and `[] ∈ Pref A`), then `ValidAcceptingTree (buildTreeSpec E ctx) t`
is inhabited, so `E.solveTreePG (buildTreeSpec E ctx) ≠ none`. -/
lemma uncomp_implies_solveTreePG_ne_none (E : Thm34Engine)
    (c : DPACode) (I : Instance) (D_m1 : ℕ) (φ : Formula ℕ ℕ ℕ ℕ)
    (hparse : parse I.tokens = some φ)
    (hCons : ∀ g ∈ Pref c.lang, ConsensusSolvableWithin Bool (leftQuot g c.lang) (D_m1 + 1))
    (hlive0 : ([] : List CommGraph) ∈ Pref c.lang)
    (t0 : LabeledTree (NodeLabel I.X1 I.X2 I.Y1 I.Y2
      (Fin ((E.compileBlock (c, I, D_m1)).1.1 + 1))))
    (ht0 : IsUncompressedComponentTree
      (let D := D_m1 + 1
       let res := E.compileBlock (c, I, D_m1)
       let dpa := toGenDPA (E.blockAlphaMinusOne I D) res.1
       ⟨dpa.init, fun q blk => dpa.step q (E.encIOBlockTyped I D blk), dpa.prio⟩)
      {q | (E.compileBlock (c, I, D_m1)).2.getD q.val false = true} t0)
    (hacc0 : IsAcceptingTree
      (let D := D_m1 + 1
       let res := E.compileBlock (c, I, D_m1)
       let dpa := toGenDPA (E.blockAlphaMinusOne I D) res.1
       ⟨dpa.init, fun q blk => dpa.step q (E.encIOBlockTyped I D blk), dpa.prio⟩) t0) :
    let res := E.compileBlock (c, I, D_m1)
    let ctx : SymCtx := (I, D_m1, res.1, res.2)
    E.solveTreePG (buildTreeSpec E ctx) ≠ none := by
  classical
  let D := D_m1 + 1
  let res := E.compileBlock (c, I, D_m1)
  let ctx : SymCtx := (I, D_m1, res.1, res.2)
  let dpa := toGenDPA (E.blockAlphaMinusOne I D) res.1
  let B : DPA (Fin (res.1.1 + 1)) (Fin D → Signal I.X1 I.X2 × (I.Y1 × I.Y2)) :=
    ⟨dpa.init, fun q blk => dpa.step q (E.encIOBlockTyped I D blk), dpa.prio⟩
  let Qlive : Set (Fin (res.1.1 + 1)) := {q | res.2.getD q.val false = true}
  have hB : IsBlockAutomaton c.lang (instFormulaOf I φ) D B Qlive :=
    E.compileBlock_spec c I D_m1 φ hparse
  let liveBlk : List (Fin D → Signal I.X1 I.X2) → Prop :=
    fun ws => graphOfHist (blockConcat ws) ∈ Pref c.lang
  let prioBlk : List (Fin D → Signal I.X1 I.X2) → ℕ :=
    fun ws => B.prio (treeState hB ht0 hlive0 ws)
  have hbc : ∀ l1 l2 : List (Fin D → Signal I.X1 I.X2),
      blockConcat (l1 ++ l2) = blockConcat l1 ++ blockConcat l2 := by
    intro l1 l2
    induction l2 using List.reverseRecOn with
    | nil => simp
    | append_singleton l2 u ih =>
      rw [← List.append_assoc, blockConcat_append_singleton, ih, blockConcat_append_singleton,
        List.append_assoc]
  have hlive_closed : ∀ ws1 ws2, ws1 <+: ws2 → liveBlk ws2 → liveBlk ws1 := by
    rintro ws1 ws2 ⟨suf, rfl⟩ hl2
    have hcat : graphOfHist (blockConcat ws1) ++ graphOfHist (blockConcat suf) ∈ Pref c.lang := by
      unfold liveBlk at hl2
      rwa [hbc, graphOfHist, List.map_append] at hl2
    exact (mem_pref_prefix hcat).1
  have hwinning : ∀ word : ℕ → (Fin D → Signal I.X1 I.X2),
      (∀ n, liveBlk (pre word n)) → ParityCond (fun n => prioBlk (pre word n)) :=
    fun word hlw => treeState_parity hB ht0 hacc0 hlive0 word hlw
  let K_prio := maxList res.1.2.2
  let rkFn : List (Fin D → Signal I.X1 I.X2) → Lex (Fin (K_prio + 1) → Ordinal.{0}) :=
    edgeRank liveBlk prioBlk hlive_closed hwinning K_prio
  let B_full := ctxBFull ctx
  let ts := buildTreeSpec E ctx
  rw [E.solveTreePG_iff_exists_tree]
  let PosData := UncompPosData I D B_full (ctxBRed ctx) liveBlk (treeState hB ht0 hlive0) rkFn
  obtain ⟨symPosOf, symActOf, pd0, hpd0_pos, hpair_spec, hchild_pd⟩ :=
    exists_uncomp_pos_system E c I D_m1 D rfl φ hCons res ctx rfl B Qlive rfl
      (fun _ _ => rfl) (fun _ => Iff.rfl) hB hlive0 t0 ht0 liveBlk rfl rkFn
  obtain ⟨labels, hlabels_def⟩ : ∃ l, l = validSymLabels ctx := ⟨_, rfl⟩
  obtain ⟨lblIdxOf, hlblIdxOf_def⟩ : ∃ f : ∀ {n : ℕ}, PosData n → Fin (ts.2.1 + 1),
      ∀ {n : ℕ} (pd : PosData n), f pd =
        ⟨cIdxOf labels (symPosOf pd, symActOf pd) + 1,
          Nat.succ_lt_succ (by
            have hmem : (symPosOf pd, symActOf pd) ∈ labels := hlabels_def ▸ (hpair_spec pd).1
            have hlt := (cIdxOf_lt_and_getElem hmem).1
            simpa [ts, buildTreeSpec, hlabels_def] using hlt)⟩ := ⟨_, fun _ => rfl⟩
  have hlblIdx_spec : ∀ {n : ℕ} (pd : PosData n),
      (lblIdxOf pd).val ≠ 0 ∧ (lblIdxOf pd).val - 1 < labels.length ∧
      labels.getD ((lblIdxOf pd).val - 1) (initSymPos, ([], [], [])) = (symPosOf pd, symActOf pd) := by
    intro n pd
    have hmem : (symPosOf pd, symActOf pd) ∈ labels := hlabels_def ▸ (hpair_spec pd).1
    obtain ⟨hlt, hget⟩ := cIdxOf_lt_and_getElem hmem
    rw [hlblIdxOf_def pd]
    dsimp only
    refine ⟨Nat.succ_ne_zero _, hlt, ?_⟩
    rw [Nat.add_sub_cancel, getD_eq_getElem labels _ _ hlt, hget]
  clear hlblIdxOf_def
  obtain ⟨pdAtRev, hpdAtRev_def⟩ : ∃ f : (revAddr : List (Fin (ts.1 + 1))) → Option (PosData revAddr.length),
      f = fun revAddr =>
        List.rec (motive := fun l => Option (PosData l.length))
          (some pd0)
          (fun d _ ih =>
            match ih with
            | none => none
            | some pd =>
              if hd : d.val < (symComponents E ctx (symPosOf pd) (symActOf pd)).length then
                some (hchild_pd pd d.val hd).choose
              else none)
          revAddr := ⟨_, rfl⟩
  have hpdAtRev_nil : pdAtRev [] = some pd0 := by rw [hpdAtRev_def]
  have hpdAtRev_cons : ∀ (d : Fin (ts.1 + 1)) (rest : List (Fin (ts.1 + 1))),
      pdAtRev (d :: rest) =
        match pdAtRev rest with
        | none => none
        | some pd =>
          if hd : d.val < (symComponents E ctx (symPosOf pd) (symActOf pd)).length then
            some (hchild_pd pd d.val hd).choose
          else none := by
    intro d rest; rw [hpdAtRev_def]
  clear hpdAtRev_def
  let tFromRev : List (Fin (ts.1 + 1)) → Fin (ts.2.1 + 1) := fun revAddr =>
    match pdAtRev revAddr with
    | none => ⟨0, Nat.succ_pos _⟩
    | some pd => lblIdxOf pd
  let t : List (Fin (ts.1 + 1)) → Fin (ts.2.1 + 1) := fun addr => tFromRev addr.reverse
  refine ⟨t, ?_, ?_, ?_⟩
  · -- `tsRootOk`
    rw [tsRootOk_buildTreeSpec, ← hlabels_def]
    have ht0_eq : t [] = lblIdxOf pd0 := by
      dsimp only [t, tFromRev, List.reverse_nil]
      rw [hpdAtRev_nil]
    rw [ht0_eq]
    obtain ⟨hne0, _, hget0⟩ := hlblIdx_spec pd0
    rw [if_neg hne0]
    change decide ((labels.getD ((lblIdxOf pd0).val - 1) (initSymPos, ([], [], []))).1 = initSymPos) = true
    rw [hget0, decide_eq_true_eq]
    exact hpd0_pos
  · -- `tsChildOk`
    intro addr d
    have ht_step_raw : t (addr ++ [d]) = tFromRev (d :: addr.reverse) :=
      congrArg tFromRev (by simp)
    have ht_cur_raw : t addr = tFromRev addr.reverse := rfl
    rw [ht_cur_raw, ht_step_raw]
    cases hopt : pdAtRev addr.reverse with
    | none =>
      have hc0 : tFromRev addr.reverse = ⟨0, Nat.succ_pos _⟩ := by
        dsimp only [tFromRev]; rw [hopt]
      have hs0 : tFromRev (d :: addr.reverse) = ⟨0, Nat.succ_pos _⟩ := by
        dsimp only [tFromRev]; rw [hpdAtRev_cons, hopt]
      rw [hc0, hs0, tsChildOk_buildTreeSpec]
      rfl
    | some pd =>
      have hc1 : tFromRev addr.reverse = lblIdxOf pd := by
        dsimp only [tFromRev]; rw [hopt]
      by_cases hd : d.val < (symComponents E ctx (symPosOf pd) (symActOf pd)).length
      · let pd' := (hchild_pd pd d.val hd).choose
        have hs1 : tFromRev (d :: addr.reverse) = lblIdxOf pd' := by
          dsimp only [tFromRev]; rw [hpdAtRev_cons, hopt]; dsimp only; rw [dif_pos hd]
        rw [hc1, hs1, tsChildOk_buildTreeSpec, ← hlabels_def]
        obtain ⟨hne, _, hget_pd⟩ := hlblIdx_spec pd
        obtain ⟨hne', _, hget_pd'⟩ := hlblIdx_spec pd'
        rw [if_neg hne, hget_pd]
        dsimp only
        rw [if_pos hd, if_neg hne']
        rw [hget_pd', getD_eq_getElem _ [] d.val hd, decide_eq_true_eq]
        exact (hchild_pd pd d.val hd).choose_spec.1
      · have hs0 : tFromRev (d :: addr.reverse) = ⟨0, Nat.succ_pos _⟩ := by
          dsimp only [tFromRev]; rw [hpdAtRev_cons, hopt]; dsimp only; rw [dif_neg hd]
        rw [hc1, hs0, tsChildOk_buildTreeSpec, ← hlabels_def]
        obtain ⟨hne, _, hget_pd⟩ := hlblIdx_spec pd
        rw [if_neg hne, hget_pd]
        dsimp only
        rw [if_neg hd]
        rfl
  · -- Branch acceptance via `folded_edges_parity`
    intro branch
    let ad : ℕ → Fin (ts.2.1 + 1) × Fin (ts.1 + 1) :=
      fun n => (t (List.ofFn (fun i : Fin n => branch i.val)), branch n)
    rw [tsDPA_buildTreeSpec_accepts_iff E ctx ad]
    rw [← hlabels_def]
    rintro ⟨iSeq, pSeq, hi0, hp_ok, hodd⟩
    let revPref : ℕ → List (Fin (ts.1 + 1)) :=
      fun n => Nat.rec [] (fun m acc => branch m :: acc) n
    have hrev_succ : ∀ n, revPref (n + 1) = branch n :: revPref n := fun _ => rfl
    have hrev_len : ∀ n, (revPref n).length = n := by
      intro n; induction n with
      | zero => rfl
      | succ n ih => rw [hrev_succ, List.length_cons, ih]
    have hpre_rev : ∀ n, (List.ofFn (fun i : Fin n => branch i.val)).reverse = revPref n := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        have hsucc : List.ofFn (fun i : Fin (n + 1) => branch i.val) =
            List.ofFn (fun i : Fin n => branch i.val) ++ [branch n] := by
          apply List.ext_getElem
          · simp
          · intro k hk1 hk2
            simp only [List.length_ofFn] at hk1
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk1) with hlt | rfl
            · rw [List.getElem_ofFn, List.getElem_append_left (by simp [hlt]), List.getElem_ofFn]
            · rw [List.getElem_ofFn, List.getElem_append_right (by simp), List.getElem_singleton]
        rw [hsucc, List.reverse_append, List.reverse_singleton, List.singleton_append, ih, hrev_succ]
    have had_t : ∀ n, (ad n).1 = tFromRev (revPref n) := by
      intro n; dsimp only [ad, t]; rw [hpre_rev n]
    -- Every `pdAtRev (revPref n)` must be `some _` because `edgeStepOk` rejects `a = 0`
    have hsome_rev : ∀ n, ∃ pd : PosData (revPref n).length, pdAtRev (revPref n) = some pd := by
      intro n
      cases hopt : pdAtRev (revPref n) with
      | some pd => exact ⟨pd, rfl⟩
      | none =>
        have hok := hp_ok n
        rw [had_t n] at hok
        dsimp only [tFromRev] at hok
        rw [hopt] at hok
        simp [edgeStepOk] at hok
    let pdRaw : ∀ n, PosData (revPref n).length := fun n => (hsome_rev n).choose
    have hpdRaw_eq : ∀ n, pdAtRev (revPref n) = some (pdRaw n) := fun n => (hsome_rev n).choose_spec
    have hstep_pd : ∀ n,
        ∃ (hd : (branch n).val < (symComponents E ctx (symPosOf (pdRaw n)) (symActOf (pdRaw n))).length)
          (hi_lt : (iSeq n).val < (pdRaw n).val.1)
          (hj_lt : (iSeq (n + 1)).val < (pdRaw (n + 1)).val.1),
          pdRaw (n + 1) = (hchild_pd (pdRaw n) (branch n).val hd).choose ∧
          let comp := (symComponents E ctx (symPosOf (pdRaw n)) (symActOf (pdRaw n)))[(branch n).val]'hd
          let ej := comp.getD (iSeq (n + 1)).val inhSymExt
          ej.1 = ((pdRaw n).val.2.2 ⟨(iSeq n).val, hi_lt⟩).val ∧
          (pSeq n).val = res.1.2.2.getD ej.2.2 0 := by
      intro n
      have h1 : pdAtRev (branch n :: revPref n) = some (pdRaw (n + 1)) := hpdRaw_eq (n + 1)
      rw [hpdAtRev_cons, hpdRaw_eq n] at h1
      dsimp only at h1
      by_cases hd : (branch n).val < (symComponents E ctx (symPosOf (pdRaw n)) (symActOf (pdRaw n))).length
      · rw [dif_pos hd] at h1
        have hpd_next : pdRaw (n + 1) = (hchild_pd (pdRaw n) (branch n).val hd).choose :=
          (Option.some.inj h1).symm
        have hok := hp_ok n
        rw [had_t n] at hok
        dsimp only [tFromRev, ad] at hok
        rw [hpdRaw_eq n] at hok
        dsimp only at hok
        obtain ⟨hne_n, hlt_lbl_n, hget_n⟩ := hlblIdx_spec (pdRaw n)
        unfold edgeStepOk at hok
        rw [if_neg hne_n, if_pos hlt_lbl_n] at hok
        change (let pa := labels.getD ((lblIdxOf (pdRaw n)).val - 1) (initSymPos, ([], [], []))
          let comps := symComponents E ctx pa.1 pa.2
          if (branch n).val < comps.length then _ else false) = true at hok
        rw [hget_n] at hok
        dsimp only at hok
        rw [if_pos hd, getD_eq_getElem _ [] (branch n).val hd] at hok
        let comp := (symComponents E ctx (symPosOf (pdRaw n)) (symActOf (pdRaw n)))[(branch n).val]'hd
        have hpos_k_n : (symPosOf (pdRaw n)).1 = (pdRaw n).val.1 := (hpair_spec (pdRaw n)).2.1
        by_cases hij : (iSeq n).val < (symPosOf (pdRaw n)).1 ∧ (iSeq (n + 1)).val < comp.length
        · rw [if_pos hij] at hok
          have hi_lt : (iSeq n).val < (pdRaw n).val.1 := by have := hij.1; omega
          have hj_lt : (iSeq (n + 1)).val < (pdRaw (n + 1)).val.1 := by
            rw [hpd_next, (hchild_pd (pdRaw n) (branch n).val hd).choose_spec.2.1]
            exact hij.2
          simp only [andBool_eq, Bool.and_eq_true, decide_eq_true_eq] at hok
          have hr_eq := (hpair_spec (pdRaw n)).2.2 ⟨(iSeq n).val, hi_lt⟩
          rw [hr_eq] at hok
          exact ⟨hd, hi_lt, hj_lt, hpd_next, hok.1, hok.2⟩
        · rw [if_neg hij] at hok; cases hok
      · rw [dif_neg hd] at h1; cases h1
    let idxAt : ∀ n, Fin (pdRaw n).val.1 := fun n => ⟨(iSeq n).val, (hstep_pd n).choose_spec.choose⟩
    let rootEdge : ℕ → List (Fin D → Signal I.X1 I.X2) :=
      fun n => (pdRaw n).val.2.1 ((pdRaw n).val.2.2 (idxAt n))
    have hstep_fold : ∀ n,
        ∃ (chosen : List (Fin D → Signal I.X1 I.X2)) (letter : Fin D → Signal I.X1 I.X2),
          rkFn chosen ≤ rkFn (rootEdge n) ∧
          rootEdge (n + 1) = chosen ++ [letter] ∧
          liveBlk (rootEdge (n + 1)) ∧
          prioBlk (rootEdge (n + 1)) = (pSeq n).val := by
      intro n
      let hd := (hstep_pd n).choose
      let hi_lt := (hstep_pd n).choose_spec.choose
      let hj_lt := (hstep_pd n).choose_spec.choose_spec.choose
      have hsp_n := (hstep_pd n).choose_spec.choose_spec.choose_spec
      rcases hsp_n with ⟨hpd_next, hej_r, hp_eq⟩
      have hj_lt' : (iSeq (n + 1)).val < ((hchild_pd (pdRaw n) (branch n).val hd).choose).val.1 := by
        rw [← hpd_next]; exact hj_lt
      have hch_spec := (hchild_pd (pdRaw n) (branch n).val hd).choose_spec.2.2
        ⟨(iSeq (n + 1)).val, hj_lt'⟩
      rcases hch_spec with ⟨ir, u_n, hej_ir, _, hblk_next, hej_q⟩
      have hir_eq : ir = (pdRaw n).val.2.2 (idxAt n) := Fin.ext (hej_ir.symm.trans hej_r)
      have hcast_blk : ∀ (x y : PosData (revPref (n + 1)).length) (hxy : x = y)
          (ix : Fin x.val.1) (iy : Fin y.val.1),
          ix.val = iy.val → x.val.2.1 ix = y.val.2.1 iy := by
        rintro x _ rfl ix iy hval
        exact congrArg x.val.2.1 (Fin.ext hval)
      have hcast : (pdRaw (n + 1)).val.2.1 (idxAt (n + 1)) =
          ((hchild_pd (pdRaw n) (branch n).val hd).choose).val.2.1
            ⟨(iSeq (n + 1)).val, hj_lt'⟩ :=
        hcast_blk (pdRaw (n + 1)) _ hpd_next (idxAt (n + 1)) ⟨(iSeq (n + 1)).val, hj_lt'⟩ rfl
      have he_n1 : (pdRaw (n + 1)).val.2.1 (idxAt (n + 1)) = rootEdge n ++ [u_n] := by
        rw [hcast, hblk_next, hir_eq]
      have hroot_len : (rootEdge n).length = n := by
        have hl := (pdRaw n).property.2.2.1 ((pdRaw n).val.2.2 (idxAt n))
        exact hl.trans (hrev_len n)
      have hprop_n1 := (pdRaw (n + 1)).property
      rcases hprop_n1 with ⟨_, _, _, _, hlive_n1, _, _, _, hr_st_n1, _, hfold_n1⟩
      have hfold_ex := hfold_n1 (revPref n).length rfl (idxAt (n + 1))
      rcases hfold_ex with ⟨ws_c, u_last, hsplit_n1, hr_n1_eq, hrk_le⟩
      rw [hrev_len n] at hsplit_n1 hrk_le
      have htake_eq : ((pdRaw (n + 1)).val.2.1 (idxAt (n + 1))).take n = rootEdge n := by
        have htk : (rootEdge n ++ [u_n]).take (rootEdge n).length = rootEdge n := List.take_left
        rwa [hroot_len, ← he_n1] at htk
      have hu_eq : u_last = u_n := by
        rw [htake_eq, he_n1] at hsplit_n1
        exact List.cons.inj (List.append_cancel_left hsplit_n1.symm) |>.1
      rw [htake_eq] at hrk_le
      rw [hu_eq] at hr_n1_eq
      refine ⟨ws_c, u_n, hrk_le, hr_n1_eq, hlive_n1 _, ?_⟩
      unfold prioBlk
      rw [hr_st_n1 (idxAt (n + 1))]
      have hq_eq : (treeState hB ht0 hlive0 ((pdRaw (n + 1)).val.2.1 (idxAt (n + 1)))).val =
          (((symComponents E ctx (symPosOf (pdRaw n)) (symActOf (pdRaw n)))[(branch n).val]'hd).getD
            (iSeq (n + 1)).val inhSymExt).2.2 := by
        rw [hcast, ← hej_q]
      have hB_prio : ∀ q : Fin (res.1.1 + 1), B.prio q = res.1.2.2.getD q.val 0 := fun _ => rfl
      rw [hB_prio, hq_eq, hp_eq]
    let chosen : ℕ → List (Fin D → Signal I.X1 I.X2) := fun n => (hstep_fold n).choose
    let letter : ℕ → Fin D → Signal I.X1 I.X2 := fun n => (hstep_fold n).choose_spec.choose
    have hfold_spec : ∀ n,
        rkFn (chosen n) ≤ rkFn (rootEdge n) ∧
        rootEdge (n + 1) = chosen n ++ [letter n] ∧
        liveBlk (rootEdge (n + 1)) ∧
        prioBlk (rootEdge (n + 1)) = (pSeq n).val :=
      fun n => (hstep_fold n).choose_spec.choose_spec
    have hpar : ParityCond (fun n => (pSeq n).val) :=
      folded_edges_parity liveBlk prioBlk hlive_closed hwinning K_prio rootEdge chosen letter
        (fun n => (pSeq n).val)
        (fun n => Nat.le_of_lt_succ (pSeq n).isLt)
        (fun n => (hfold_spec n).1)
        (fun n => (hfold_spec n).2.1)
        (fun n => (hfold_spec n).2.2.1)
        (fun n => (hfold_spec n).2.2.2)
    exact not_parityCond_and_oddParityCond _ ⟨hpar, hodd⟩

end DistLTLSynth.Char.Lemma312Aux

open DistLTLSynth.Char DistLTLSynth.Char.Lemma312Aux in
theorem solution (E : Thm34Engine)
    (c : DPACode) (I : Instance) (D_m1 : ℕ) (φ : Formula ℕ ℕ ℕ ℕ)
    (hparse : parse I.tokens = some φ)
    (hCons : ∀ g ∈ Pref c.lang, ConsensusSolvableWithin Bool (leftQuot g c.lang) (D_m1 + 1))
    (hlive0 : ([] : List CommGraph) ∈ Pref c.lang)
    (t0 : LabeledTree (NodeLabel I.X1 I.X2 I.Y1 I.Y2
      (Fin ((E.compileBlock (c, I, D_m1)).1.1 + 1))))
    (ht0 : IsUncompressedComponentTree
      (let D := D_m1 + 1
       let res := E.compileBlock (c, I, D_m1)
       let dpa := toGenDPA (E.blockAlphaMinusOne I D) res.1
       ⟨dpa.init, fun q blk => dpa.step q (E.encIOBlockTyped I D blk), dpa.prio⟩)
      {q | (E.compileBlock (c, I, D_m1)).2.getD q.val false = true} t0)
    (hacc0 : IsAcceptingTree
      (let D := D_m1 + 1
       let res := E.compileBlock (c, I, D_m1)
       let dpa := toGenDPA (E.blockAlphaMinusOne I D) res.1
       ⟨dpa.init, fun q blk => dpa.step q (E.encIOBlockTyped I D blk), dpa.prio⟩) t0) :
    let res := E.compileBlock (c, I, D_m1)
    let ctx : SymCtx := (I, D_m1, res.1, res.2)
    E.solveTreePG (buildTreeSpec E ctx) ≠ none :=
  uncomp_implies_solveTreePG_ne_none E c I D_m1 φ hparse hCons hlive0 t0 ht0 hacc0
