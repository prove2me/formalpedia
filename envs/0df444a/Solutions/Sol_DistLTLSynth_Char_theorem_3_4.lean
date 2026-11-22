-- Prove2me | solution 1 for DistLTLSynth.Char.theorem_3_4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T12:45:58.727837+00:00
-- url     : https://prove2.me/submissions/d03f819c-f026-4561-8350-007e5ea796d0

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL
import Definitions.Def_DistLTLSynth_Char_Geometric
import Definitions.Def_DistLTLSynth_Char_Automata
import Definitions.Def_DistLTLSynth_Char_Consensus
import Definitions.Def_DistLTLSynth_Char_ComponentTree
import Definitions.Def_DistLTLSynth_Char_SynthesisEngine
import Definitions.Def_DistLTLSynth_Char_SymbolicArena
import Theorems.Thm_DistLTLSynth_Char_lemma_3_6
import Theorems.Thm_DistLTLSynth_Char_lemma_3_7
import Theorems.Thm_DistLTLSynth_Char_lemma_3_9
import Theorems.Thm_DistLTLSynth_Char_lemma_6_15
import Theorems.Thm_DistLTLSynth_Char_nbw_determinization
import Theorems.Thm_DistLTLSynth_Char_regular_tree_parity_solver
import Theorems.Thm_DistLTLSynth_Char_lemma_3_13
import Theorems.Thm_DistLTLSynth_Char_lemma_3_12

set_option autoImplicit false

namespace DistLTLSynth.Char.Thm34Aux

open DistLTLSynth.Char

lemma primrec_parseOk : Primrec parseOk :=
  DistLTLSynth.Char.lemma_3_13.1

lemma parseOk_iff_exists_parse (ts : List Token) :
    parseOk ts = true ↔ ∃ φ, parse ts = some φ :=
  DistLTLSynth.Char.lemma_3_13.2.1 ts

lemma fRealizes_instFormulaOf_iff (I : Instance) (φ : Formula ℕ ℕ ℕ ℕ)
    (A : Set (ℕ → CommGraph)) (f : Algorithm I.X1 I.X2 I.Y1 I.Y2) :
    FRealizes f A (instFormulaOf I φ) ↔ RealizesLang f A (I.Lang φ) :=
  DistLTLSynth.Char.lemma_3_13.2.2.1 I φ A f

lemma primrec_validSymLabels : Primrec validSymLabels :=
  DistLTLSynth.Char.lemma_3_13.2.2.2.1

lemma mem_validSymLabels_iff (c : SymCtx) (pa : SymPosCode × SymActCode) :
    pa ∈ validSymLabels c ↔
      pa.1 ∈ allSymPos c ∧ pa.2 ∈ allSymActsFor c pa.1 ∧ actValid c pa.1 pa.2 = true :=
  DistLTLSynth.Char.lemma_3_13.2.2.2.2.2.1 c pa

lemma primrec_symNextStatePacked (E : Thm34Engine) : Primrec (symNextStatePacked E) :=
  DistLTLSynth.Char.lemma_3_13.2.2.2.2.2.2.1 E

lemma primrec_symComponentsPacked (E : Thm34Engine) : Primrec (symComponentsPacked E) :=
  DistLTLSynth.Char.lemma_3_13.2.2.2.2.2.2.2.1 E

lemma primrec_buildTreeSpec (E : Thm34Engine) : Primrec (buildTreeSpec E) :=
  DistLTLSynth.Char.lemma_3_13.2.2.2.2.2.2.2.2.1 E

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

lemma symLiveExts_nodup_and_length (E : Thm34Engine) (ctx : SymCtx)
    (pos : SymPosCode) (act : SymActCode)
    (hfix_le : (fixedIdxs pos act).length ≤ ctxBRed ctx) :
    (symLiveExts E ctx pos act).Nodup ∧
      (symLiveExts E ctx pos act).length ≤ ctxBFull ctx :=
  DistLTLSynth.Char.lemma_3_13.2.2.2.2.2.2.2.2.2.2.2.2.2.1 E ctx pos act hfix_le

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

lemma childSymPos_access (I : Instance) (pos : SymPosCode) (comp : List SymExtElem) :
    let pos' := childSymPos I pos comp
    pos'.1 = comp.length ∧
    (∀ a (ha : a < comp.length) b (hb : b < comp.length),
      eq1At pos' a b = (extEqNat I pos (comp[a]'ha).1 (comp[a]'ha).2.1 (comp[b]'hb).1 (comp[b]'hb).2.1).1) ∧
    (∀ a (ha : a < comp.length) b (hb : b < comp.length),
      eq2At pos' a b = (extEqNat I pos (comp[a]'ha).1 (comp[a]'ha).2.1 (comp[b]'hb).1 (comp[b]'hb).2.1).2) ∧
    (∀ a (ha : a < comp.length), stateAt pos' a = (comp[a]'ha).2.2) :=
  DistLTLSynth.Char.lemma_3_13.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 I pos comp

lemma extEqFrom_of_hom (I : Instance) {h1 h2 : List (Signal I.X1 I.X2)} (hlen : h1.length = h2.length)
    {b1 b2 : Bool} (hb1 : view1 h1 = view1 h2 → b1 = true) (hb2 : view2 h1 = view2 h2 → b2 = true)
    (w1 w2 : List ℕ) :
    (view1 (h1 ++ decHist I w1) = view1 (h2 ++ decHist I w2) → (extEqFrom I b1 b2 w1 w2).1 = true) ∧
      (view2 (h1 ++ decHist I w1) = view2 (h2 ++ decHist I w2) → (extEqFrom I b1 b2 w1 w2).2 = true) :=
  DistLTLSynth.Char.lemma_3_13.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 I hlen hb1 hb2 w1 w2

lemma mem_compIdxOf_iff {α : Type} (inh : α) (S : List α) (adj : α → α → Bool)
    {i : ℕ} (hi : i < S.length) (y : ℕ) :
    y ∈ compIdxOf inh S adj i ↔
      y < S.length ∧
        Relation.ReflTransGen
          (fun a b => a < S.length ∧ b < S.length ∧ adj (S.getD a inh) (S.getD b inh) = true) i y :=
  DistLTLSynth.Char.lemma_3_13.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 inh S adj hi y

lemma compIdxOf_nodup_and_lt {α : Type} (inh : α) (S : List α) (adj : α → α → Bool)
    {i : ℕ} (hi : i < S.length) :
    (compIdxOf inh S adj i).Nodup ∧ i ∈ compIdxOf inh S adj i ∧
      (compIdxOf inh S adj i).length ≤ S.length ∧
      ∀ y ∈ compIdxOf inh S adj i, y < S.length :=
  DistLTLSynth.Char.lemma_3_13.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 inh S adj hi

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
    E.solveTreePG (buildTreeSpec E ctx) ≠ none :=
  DistLTLSynth.Char.lemma_3_12 E c I D_m1 φ hparse hCons hlive0 t0 ht0 hacc0

lemma encode_fin_val {n : ℕ} (x : Fin n) : Encodable.encode x = x.val := rfl

lemma primrec₂_natPair : Primrec₂ Nat.pair := Primrec.encode

lemma iterNat_succ {α : Type} (g : α → α) (m : ℕ) (x : α) :
    iterNat g (m + 1) x = g (iterNat g m x) := by
  simp [iterNat, List.range_succ]

lemma iterNat_comm {α : Type} (g : α → α) (m : ℕ) (x : α) :
    g (iterNat g m x) = iterNat g m (g x) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [iterNat_succ, iterNat_succ, ih]

lemma list_sections_primrec {α : Type} [Primcodable α] :
    Primrec (List.sections (α := α)) := by
  have hf : Primrec (fun xs : List (List α) => xs.foldr
      (fun choices tails => tails.flatMap (fun tail => choices.map (fun a => a :: tail))) [[]]) :=
    Primrec.list_foldr Primrec.id (Primrec.const [[]])
      (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd)
        (Primrec.list_map (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂).to₂).to₂
  exact hf.of_eq (fun xs => by induction xs <;> simp_all [List.sections])

lemma wordsOf_primrec {α : Type} [Primcodable α] : Primrec₂ (wordsOf (α := α)) :=
  list_sections_primrec.comp
    (Primrec.list_map (Primrec.list_range.comp Primrec.snd) (Primrec.fst.comp Primrec.fst).to₂)

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

lemma primrec_decide {α : Type} [Primcodable α] {p : α → Prop} [DecidablePred p]
    (hp : PrimrecPred p) :
    Primrec (fun x => decide (p x)) :=
  (Primrec.ite hp (Primrec.const true) (Primrec.const false)).of_eq fun x => by
    by_cases h : p x <;> simp [h]

lemma mem_dedupList {α : Type} [DecidableEq α] (xs : List α) (a : α) :
    a ∈ dedupList xs ↔ a ∈ xs := by
  induction xs generalizing a with
  | nil => simp [dedupList]
  | cons x xs ih =>
    change a ∈ (if x ∈ dedupList xs then dedupList xs else x :: dedupList xs) ↔ a ∈ x :: xs
    split_ifs with h
    · have hx := (ih x).mp h
      simp only [ih, List.mem_cons]
      exact ⟨Or.inr, fun hc => hc.elim (fun he => he ▸ hx) id⟩
    · simp only [List.mem_cons, ih]

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

private lemma sNat_0_le : sNat 0 ≤ 2 := by decide

private lemma sNat_1_le : sNat 1 ≤ 2 := by decide

private lemma sNat_2_gt : ¬ sNat 2 ≤ 2 := by decide

private lemma sNat_3_gt : ¬ sNat 3 ≤ 2 := by decide

private lemma sNat_4_gt : ¬ sNat 4 ≤ 2 := by decide

private lemma sNat_5_gt : ¬ sNat 5 ≤ 2 := by decide

lemma parentNat_encode {X1 X2 : Type} [Encodable X1] [Encodable X2] (v : View X1 X2) :
    parentNat (Encodable.encode v) = Encodable.encode (parentView v) := by
  cases v with
  | I1 =>
    rw [encode_view_I1, show parentView (View.I1 : View X1 X2) = View.I1 from rfl, encode_view_I1]
    unfold parentNat encI1; rw [Nat.unpair_pair, if_pos sNat_0_le]
  | I2 =>
    rw [encode_view_I2, show parentView (View.I2 : View X1 X2) = View.I2 from rfl, encode_view_I2]
    unfold parentNat encI2; rw [Nat.unpair_pair, if_pos sNat_1_le]
  | N1 x1 u =>
    rw [encode_view_N1]; unfold parentNat encN1 parentView
    simp only [Nat.unpair_pair, if_neg sNat_2_gt, Nat.add_sub_cancel]
  | N2 x2 v =>
    rw [encode_view_N2]; unfold parentNat encN2 parentView
    simp only [Nat.unpair_pair, if_neg sNat_3_gt, Nat.add_sub_cancel]
  | C1 x1 u x2 v =>
    rw [encode_view_C1]; unfold parentNat encC1 parentView
    simp only [Nat.unpair_pair, if_neg sNat_4_gt, Nat.add_sub_cancel]
  | C2 x2 v x1 u =>
    rw [encode_view_C2]; unfold parentNat encC2 parentView
    simp only [Nat.unpair_pair, if_neg sNat_5_gt, Nat.add_sub_cancel]

lemma vdepth_le_encode {X1 X2 : Type} [Encodable X1] [Encodable X2] (v : View X1 X2) :
    vdepth v ≤ Encodable.encode v := by
  induction v with
  | I1 => exact Nat.zero_le _
  | I2 => exact Nat.zero_le _
  | N1 x1 u ih =>
    rw [encode_view_N1]; unfold vdepth encN1
    have h1 := Nat.left_le_pair (Encodable.encode u + 1) 0
    have h2 := Nat.right_le_pair (sNat (Encodable.encode x1)) (Nat.pair (Encodable.encode u + 1) 0)
    have h3 := Nat.right_le_pair (sNat 2) (Nat.pair (sNat (Encodable.encode x1)) (Nat.pair (Encodable.encode u + 1) 0))
    omega
  | N2 x2 v ih =>
    rw [encode_view_N2]; unfold vdepth encN2
    have h1 := Nat.left_le_pair (Encodable.encode v + 1) 0
    have h2 := Nat.right_le_pair (sNat (Encodable.encode x2)) (Nat.pair (Encodable.encode v + 1) 0)
    have h3 := Nat.right_le_pair (sNat 3) (Nat.pair (sNat (Encodable.encode x2)) (Nat.pair (Encodable.encode v + 1) 0))
    omega
  | C1 x1 u x2 v ihu _ =>
    rw [encode_view_C1]; unfold vdepth encC1
    have h1 := Nat.left_le_pair (Encodable.encode u + 1) (Nat.pair (sNat (Encodable.encode x2)) (Nat.pair (Encodable.encode v + 1) 0))
    have h2 := Nat.right_le_pair (sNat (Encodable.encode x1))
      (Nat.pair (Encodable.encode u + 1) (Nat.pair (sNat (Encodable.encode x2)) (Nat.pair (Encodable.encode v + 1) 0)))
    have h3 := Nat.right_le_pair (sNat 4)
      (Nat.pair (sNat (Encodable.encode x1))
        (Nat.pair (Encodable.encode u + 1) (Nat.pair (sNat (Encodable.encode x2)) (Nat.pair (Encodable.encode v + 1) 0))))
    omega
  | C2 x2 v x1 u ihv _ =>
    rw [encode_view_C2]; unfold vdepth encC2
    have h1 := Nat.left_le_pair (Encodable.encode v + 1) (Nat.pair (sNat (Encodable.encode x1)) (Nat.pair (Encodable.encode u + 1) 0))
    have h2 := Nat.right_le_pair (sNat (Encodable.encode x2))
      (Nat.pair (Encodable.encode v + 1) (Nat.pair (sNat (Encodable.encode x1)) (Nat.pair (Encodable.encode u + 1) 0)))
    have h3 := Nat.right_le_pair (sNat 5)
      (Nat.pair (sNat (Encodable.encode x2))
        (Nat.pair (Encodable.encode v + 1) (Nat.pair (sNat (Encodable.encode x1)) (Nat.pair (Encodable.encode u + 1) 0))))
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
        (Encodable.encode (View.I1 : View X1 X2), d) := fun k => by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [iterNat_succ, ih]; unfold depthStepNat; rw [encode_view_I1]; unfold encI1
        simp only [Nat.unpair_pair, if_pos sNat_0_le]
    rw [hfix m]; simp [vdepth]
  | I2 =>
    intro m d _
    have hfix : ∀ k, iterNat depthStepNat k (Encodable.encode (View.I2 : View X1 X2), d) =
        (Encodable.encode (View.I2 : View X1 X2), d) := fun k => by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [iterNat_succ, ih]; unfold depthStepNat; rw [encode_view_I2]; unfold encI2
        simp only [Nat.unpair_pair, if_pos sNat_1_le]
    rw [hfix m]; simp [vdepth]
  | N1 x1 u ih =>
    intro m d hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [vdepth] at hm; omega⟩
    rw [iterNat_succ, iterNat_comm depthStepNat]
    have hstep : depthStepNat (Encodable.encode (View.N1 x1 u), d) = (Encodable.encode u, d + 1) := by
      have hp := parentNat_encode (View.N1 x1 u); simp only [parentView] at hp
      unfold depthStepNat
      have hgt : ¬ (Encodable.encode (View.N1 x1 u)).unpair.1 ≤ 2 := by
        rw [encode_view_N1]; unfold encN1; rw [Nat.unpair_pair]; exact sNat_2_gt
      rw [if_neg hgt, hp]
    rw [hstep, ih k (d + 1) (by simp [vdepth] at hm; omega)]; simp [vdepth]; omega
  | N2 x2 v ih =>
    intro m d hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [vdepth] at hm; omega⟩
    rw [iterNat_succ, iterNat_comm depthStepNat]
    have hstep : depthStepNat (Encodable.encode (View.N2 x2 v), d) = (Encodable.encode v, d + 1) := by
      have hp := parentNat_encode (View.N2 x2 v); simp only [parentView] at hp
      unfold depthStepNat
      have hgt : ¬ (Encodable.encode (View.N2 x2 v)).unpair.1 ≤ 2 := by
        rw [encode_view_N2]; unfold encN2; rw [Nat.unpair_pair]; exact sNat_3_gt
      rw [if_neg hgt, hp]
    rw [hstep, ih k (d + 1) (by simp [vdepth] at hm; omega)]; simp [vdepth]; omega
  | C1 x1 u x2 v ihu _ =>
    intro m d hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [vdepth] at hm; omega⟩
    rw [iterNat_succ, iterNat_comm depthStepNat]
    have hstep : depthStepNat (Encodable.encode (View.C1 x1 u x2 v), d) = (Encodable.encode u, d + 1) := by
      have hp := parentNat_encode (View.C1 x1 u x2 v); simp only [parentView] at hp
      unfold depthStepNat
      have hgt : ¬ (Encodable.encode (View.C1 x1 u x2 v)).unpair.1 ≤ 2 := by
        rw [encode_view_C1]; unfold encC1; rw [Nat.unpair_pair]; exact sNat_4_gt
      rw [if_neg hgt, hp]
    rw [hstep, ihu k (d + 1) (by simp [vdepth] at hm; omega)]; simp [vdepth]; omega
  | C2 x2 v x1 u ihv _ =>
    intro m d hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [vdepth] at hm; omega⟩
    rw [iterNat_succ, iterNat_comm depthStepNat]
    have hstep : depthStepNat (Encodable.encode (View.C2 x2 v x1 u), d) = (Encodable.encode v, d + 1) := by
      have hp := parentNat_encode (View.C2 x2 v x1 u); simp only [parentView] at hp
      unfold depthStepNat
      have hgt : ¬ (Encodable.encode (View.C2 x2 v x1 u)).unpair.1 ≤ 2 := by
        rw [encode_view_C2]; unfold encC2; rw [Nat.unpair_pair]; exact sNat_5_gt
      rw [if_neg hgt, hp]
    rw [hstep, ihv k (d + 1) (by simp [vdepth] at hm; omega)]; simp [vdepth]; omega

lemma vdepthNat_encode {X1 X2 : Type} [Encodable X1] [Encodable X2] (v : View X1 X2) :
    vdepthNat (Encodable.encode v) = vdepth v := by
  unfold vdepthNat
  simpa using iterNat_depthStepNat_encode v (Encodable.encode v) 0 (vdepth_le_encode v)

section ViewsNatEnc

attribute [local irreducible] encN1 encN2 encC1 encC2

def viewStepSigNat (uv : ℕ × ℕ) (sig : ℕ × ℕ × CommGraph) : ℕ × ℕ :=
  match sig with
  | (x1, x2, .oneToTwo) => (encN1 x1 uv.1, encC2 x2 uv.2 x1 uv.1)
  | (x1, x2, .both) => (encC1 x1 uv.1 x2 uv.2, encC2 x2 uv.2 x1 uv.1)
  | (x1, x2, .twoToOne) => (encC1 x1 uv.1 x2 uv.2, encN2 x2 uv.2)

lemma primrec_viewStepSigNat : Primrec₂ viewStepSigNat := by
  have hx1 : Primrec fun p : (ℕ × ℕ) × (ℕ × ℕ × CommGraph) => p.2.1 := Primrec.fst.comp Primrec.snd
  have hx2 : Primrec fun p : (ℕ × ℕ) × (ℕ × ℕ × CommGraph) => p.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hg : Primrec fun p : (ℕ × ℕ) × (ℕ × ℕ × CommGraph) => p.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have huv1 : Primrec fun p : (ℕ × ℕ) × (ℕ × ℕ × CommGraph) => p.1.1 := Primrec.fst.comp Primrec.fst
  have huv2 : Primrec fun p : (ℕ × ℕ) × (ℕ × ℕ × CommGraph) => p.1.2 := Primrec.snd.comp Primrec.fst
  have hc1 := primrec_encC1.comp (Primrec.pair (Primrec.pair hx1 huv1) (Primrec.pair hx2 huv2))
  have hc2 := primrec_encC2.comp (Primrec.pair (Primrec.pair hx2 huv2) (Primrec.pair hx1 huv1))
  have hn1 := primrec_encN1.comp hx1 huv1
  have hn2 := primrec_encN2.comp hx2 huv2
  exact (Primrec.ite (Primrec.eq.comp hg (Primrec.const CommGraph.oneToTwo))
    (Primrec.pair hn1 hc2)
    (Primrec.ite (Primrec.eq.comp hg (Primrec.const CommGraph.both))
      (Primrec.pair hc1 hc2)
      (Primrec.pair hc1 hn2))).of_eq fun ⟨uv, x1, x2, g⟩ => by
    cases g <;> rfl

def viewsSigNat (h : List (ℕ × ℕ × CommGraph)) : ℕ × ℕ :=
  h.foldl viewStepSigNat (encI1, encI2)

lemma primrec_viewsSigNat : Primrec viewsSigNat :=
  Primrec.list_foldl Primrec.id (Primrec.const (encI1, encI2))
    (primrec_viewStepSigNat.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

lemma viewsSigNat_eq_encode {a b : ℕ} (h : List (Signal (Fin a) (Fin b))) :
    viewsSigNat (h.map fun s => (s.1.val, s.2.1.val, s.2.2)) =
      (Encodable.encode (view1 h), Encodable.encode (view2 h)) := by
  unfold viewsSigNat
  suffices ∀ uv : View (Fin a) (Fin b) × View (Fin a) (Fin b),
      (h.map fun s => (s.1.val, s.2.1.val, s.2.2)).foldl viewStepSigNat
          (Encodable.encode uv.1, Encodable.encode uv.2) =
        (Encodable.encode (h.foldl viewStep uv).1, Encodable.encode (h.foldl viewStep uv).2) by
    simpa [view1, view2, views, encode_view_I1, encode_view_I2] using this (View.I1, View.I2)
  induction h with
  | nil => intro _; rfl
  | cons s tl ih =>
    intro uv
    rcases s with ⟨x1, x2, g⟩
    simp only [List.map_cons, List.foldl_cons]
    have hstep : viewStepSigNat (Encodable.encode uv.1, Encodable.encode uv.2) (x1.val, x2.val, g) =
        (Encodable.encode (viewStep uv (x1, x2, g)).1, Encodable.encode (viewStep uv (x1, x2, g)).2) := by
      cases g <;> simp [viewStepSigNat, viewStep, encode_view_N1, encode_view_N2,
        encode_view_C1, encode_view_C2, encode_fin_val]
    rw [hstep]
    exact ih (viewStep uv (x1, x2, g))

end ViewsNatEnc

def encConstCode : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * (2 * Nat.pair 1 (encConstCode n) + 1) + 4

lemma encConstCode_eq (n : ℕ) : encConstCode n = Encodable.encode (Nat.Partrec.Code.const n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 2 * (2 * Nat.pair 1 (encConstCode n) + 1) + 4 =
      Encodable.encode (Nat.Partrec.Code.comp .succ (Nat.Partrec.Code.const n))
    rw [ih]; rfl

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

lemma computable_curry_primcodable {α : Type} [Primcodable α] (U : Nat.Partrec.Code) :
    Computable fun a : α => U.curry (Encodable.encode a) := by
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
    intro n; dsimp only [encCurry, eU, eId]; rw [encConstCode_eq]; rfl
  have hcomp : Computable fun a : α =>
      Denumerable.ofNat Nat.Partrec.Code (encCurry (Encodable.encode a)) :=
    (Computable.ofNat Nat.Partrec.Code).comp (henc_prim.comp Primrec.encode).to_comp
  exact hcomp.of_eq fun a => by rw [henc_eq, Denumerable.ofNat_encode]

lemma exists_curried_code {α : Type} [Primcodable α] {run : α × ℕ → ℕ} (hrun : Computable run) :
    ∃ con : α → Nat.Partrec.Code, Computable con ∧
      ∀ (a : α) (x : ℕ), (con a).eval x = Part.some (run (a, x)) := by
  let runNat : ℕ → ℕ := fun z =>
    match Encodable.decode (α := α) z.unpair.1 with
    | some a => run (a, z.unpair.2)
    | none => 0
  have hrunNat : Computable runNat := by
    have hdec : Computable fun z : ℕ => Encodable.decode (α := α) z.unpair.1 :=
      (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair)).to_comp
    have hsome : Computable₂ fun (z : ℕ) (a : α) => run (a, z.unpair.2) :=
      hrun.comp (Computable.snd.pair ((Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.fst))
    exact (Computable.option_casesOn hdec (Computable.const 0) hsome).of_eq fun z => by
      dsimp only [runNat]
      cases Encodable.decode (α := α) z.unpair.1 <;> rfl
  rcases Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hrunNat.partrec) with ⟨U, hU⟩
  refine ⟨fun a => U.curry (Encodable.encode a), computable_curry_primcodable U, ?_⟩
  intro a x
  rw [Nat.Partrec.Code.eval_curry, hU]
  simp [runNat, Nat.unpair_pair, Encodable.encodek]

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

lemma reachableInB_zero {X1 X2 Y1 Y2 QB : Type} [Inhabited X1] [Inhabited X2]
    [Inhabited Y1] [Inhabited Y2] {D : ℕ}
    (B : DPA QB (Fin D → Signal X1 X2 × (Y1 × Y2))) :
    ReachableInB B 0 [] B.init :=
  ⟨by simp, fun _ => ((default, default, .both), (default, default)), by simp [pre], rfl⟩

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

lemma getD_eq_getElem {α : Type} (l : List α) (d : α) (i : ℕ) (hi : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

lemma getD_of_ge {α : Type} (l : List α) (d : α) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

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

lemma parityCond_or_oddParityCond_of_bdd (c : ℕ → ℕ) (K : ℕ)
    (hbdd : ∀ n : ℕ, c n ≤ K) :
    ParityCond c ∨ OddParityCond c := by
  obtain ⟨p, _, hfreq, hev⟩ := bounded_seq_min_inf_often K c hbdd
  rcases Nat.even_or_odd p with heven | hodd
  · exact Or.inl ⟨p, heven, hfreq, hev⟩
  · exact Or.inr ⟨p, hodd, hfreq, hev⟩

lemma oddParityCond_iff_not_parityCond_of_bdd (c : ℕ → ℕ) (K : ℕ)
    (hbdd : ∀ n : ℕ, c n ≤ K) :
    OddParityCond c ↔ ¬ ParityCond c := by
  constructor
  · intro ho hp
    exact not_parityCond_and_oddParityCond c ⟨hp, ho⟩
  · intro hnp
    rcases parityCond_or_oddParityCond_of_bdd c K hbdd with hp | ho
    · exact False.elim (hnp hp)
    · exact ho

lemma parityCond_shift (c : ℕ → ℕ) (d : ℕ) :
    ParityCond c ↔ ParityCond (fun n => c (d + n)) := by
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

lemma cMax_eq_max (a b : ℕ) : cMax a b = max a b := by
  unfold cMax
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (Nat.le_of_not_le h)).symm

lemma le_maxList_of_mem {xs : List ℕ} {x : ℕ} (hx : x ∈ xs) : x ≤ maxList xs := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    simp only [maxList, List.foldr_cons, cMax_eq_max]
    rcases List.mem_cons.mp hx with rfl | htl
    · exact le_max_left _ _
    · exact le_trans (ih htl) (le_max_right _ _)

lemma getD_zero_le_maxList (xs : List ℕ) (i : ℕ) : xs.getD i 0 ≤ maxList xs := by
  by_cases hi : i < xs.length
  · rw [getD_eq_getElem xs 0 i hi]
    exact le_maxList_of_mem (List.getElem_mem hi)
  · rw [getD_of_ge xs 0 i (Nat.not_lt.mp hi)]
    exact Nat.zero_le _

lemma myPow_eq (b e : ℕ) : myPow b e = b ^ e := by
  unfold myPow
  induction e with
  | zero => simp
  | succ e ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih, pow_succ]

@[simp] lemma andBool_eq (a b : Bool) : andBool a b = (a && b) := by cases a <;> cases b <;> rfl

@[simp] lemma orBool_eq (a b : Bool) : orBool a b = (a || b) := by cases a <;> cases b <;> rfl

@[simp] lemma notBool_eq (a : Bool) : notBool a = !a := by cases a <;> rfl

lemma filter_primrec {X α : Type} [Primcodable X] [Primcodable α]
    {xs : X → List α} {p : X → α → Bool}
    (hxs : Primrec xs) (hp : Primrec fun q : X × α => p q.1 q.2) :
    Primrec fun x : X => (xs x).filter (p x) :=
  (Primrec.list_flatMap hxs
    (Primrec.ite (Primrec.eq.comp hp (Primrec.const true))
      (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
      (Primrec.const [])).to₂).of_eq fun x => by
    induction xs x with
    | nil => rfl
    | cons a l ih =>
      simp only [List.filter_cons, List.flatMap_cons]
      cases p x a <;> simp [ih]

@[simp] lemma cIdxOf_nil {α : Type} [DecidableEq α] (x : α) : cIdxOf ([] : List α) x = 0 := rfl

@[simp] lemma cIdxOf_cons {α : Type} [DecidableEq α] (y : α) (ys : List α) (x : α) :
    cIdxOf (y :: ys) x = if x = y then 0 else cIdxOf ys x + 1 := rfl

lemma primrec₂_cIdxOf {α : Type} [Primcodable α] [DecidableEq α] :
    Primrec₂ (cIdxOf (α := α)) :=
  Primrec.list_foldr Primrec.fst (Primrec.const 0)
    (Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.const 0)
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))).to₂

lemma cIdxOf_lt_iff_mem {α : Type} [DecidableEq α] (xs : List α) (x : α) :
    cIdxOf xs x < xs.length ↔ x ∈ xs := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    by_cases hxy : x = y
    · subst hxy; simp
    · simp [hxy, ih]

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

lemma primrec_instK1 : Primrec Instance.k1 := Primrec.fst.comp Primrec.of_equiv

lemma primrec_instK2 : Primrec Instance.k2 := Primrec.fst.comp (Primrec.snd.comp Primrec.of_equiv)

lemma primrec_instM1 : Primrec Instance.m1 :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.of_equiv))

lemma primrec_instM2 : Primrec Instance.m2 :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.of_equiv)))

lemma primrec_instTokens : Primrec Instance.tokens :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.of_equiv)))

lemma sigCard_pos (I : Instance) : 0 < sigCard I := by unfold sigCard; positivity

lemma primrec_sigCard : Primrec sigCard :=
  Primrec.nat_mul.comp
    (Primrec.nat_mul.comp (Primrec.succ.comp primrec_instK1) (Primrec.succ.comp primrec_instK2))
    (Primrec.const 3)

lemma primrec_decSigG : Primrec decSigG := Primrec.nat_mod.comp Primrec.id (Primrec.const 3)

lemma primrec₂_decSigX2 : Primrec₂ decSigX2 :=
  Primrec.nat_mod.comp (Primrec.nat_div.comp Primrec.snd (Primrec.const 3))
    (Primrec.succ.comp (primrec_instK2.comp Primrec.fst))

lemma primrec₂_decSigX1 : Primrec₂ decSigX1 :=
  Primrec.nat_mod.comp
    (Primrec.nat_div.comp (Primrec.nat_div.comp Primrec.snd (Primrec.const 3))
      (Primrec.succ.comp (primrec_instK2.comp Primrec.fst)))
    (Primrec.succ.comp (primrec_instK1.comp Primrec.fst))

lemma primrec_decGraph : Primrec decGraph :=
  Primrec.ite (Primrec.eq.comp primrec_decSigG (Primrec.const 0)) (Primrec.const CommGraph.oneToTwo)
    (Primrec.ite (Primrec.eq.comp primrec_decSigG (Primrec.const 1)) (Primrec.const CommGraph.both)
      (Primrec.const CommGraph.twoToOne))

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

@[simp] lemma decHist_encHist (I : Instance) (h : List (Signal I.X1 I.X2)) :
    decHist I (encHist I h) = h := by
  simp [decHist, encHist, List.map_map, Function.comp_def, decSigTyped_encSigTyped]

@[simp] lemma decBlock_encBlock (I : Instance) {D : ℕ} (u : Fin D → Signal I.X1 I.X2) :
    decBlock I D (encBlock I u) = u := by
  funext t
  unfold decBlock encBlock encHist
  rw [getD_eq_getElem _ 0 t.val (by simp [t.isLt])]
  simp [decSigTyped_encSigTyped]

lemma primrec₂_nonemptyExtWords : Primrec₂ nonemptyExtWords :=
  Primrec.list_flatMap
    (Primrec.list_map (Primrec.list_range.comp Primrec.snd) (Primrec.succ.comp Primrec.snd).to₂)
    (wordsOf_primrec.comp
      (Primrec.list_range.comp (primrec_sigCard.comp (Primrec.fst.comp Primrec.fst)))
      Primrec.snd).to₂

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

lemma encBlock_mem_fullBlocks (I : Instance) {D : ℕ} (u : Fin D → Signal I.X1 I.X2) :
    encBlock I u ∈ fullBlocks I D := by
  rw [mem_fullBlocks_iff]
  refine ⟨by simp [encBlock, encHist], ?_⟩
  intro x hx
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx
  exact encSigTyped_lt I s

def viewsNatOfCode (I : Instance) (w : List ℕ) : ℕ × ℕ :=
  viewsSigNat (w.map fun s => (decSigX1 I s, decSigX2 I s, decGraph s))

lemma primrec₂_viewsNatOfCode : Primrec₂ viewsNatOfCode :=
  primrec_viewsSigNat.comp
    (Primrec.list_map Primrec.snd
      ((primrec₂_decSigX1.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).pair
        ((primrec₂_decSigX2.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).pair
          (primrec_decGraph.comp Primrec.snd))).to₂)

lemma viewsNatOfCode_eq_encode (I : Instance) (w : List ℕ) :
    viewsNatOfCode I w =
      (Encodable.encode (view1 (decHist I w)), Encodable.encode (view2 (decHist I w))) := by
  unfold viewsNatOfCode decHist
  rw [← viewsSigNat_eq_encode (w.map (decSigTyped I))]
  simp [List.map_map, Function.comp_def, decSigTyped]

lemma ctxBlockCard_pos (c : SymCtx) : 0 < ctxBlockCard c := by
  unfold ctxBlockCard; rw [myPow_eq]; exact Nat.pow_pos (sigCard_pos (ctxI c))

lemma ctxBRed_pos (c : SymCtx) : 0 < ctxBRed c := by
  unfold ctxBRed
  rw [myPow_eq]
  exact Nat.mul_pos (Nat.pow_pos (by unfold ctxQBCard; omega)) (ctxBlockCard_pos c)

lemma ctxBFull_pos (c : SymCtx) : 0 < ctxBFull c :=
  Nat.mul_pos (ctxBRed_pos c) (ctxBlockCard_pos c)

lemma primrec_ctxI : Primrec ctxI := Primrec.fst

lemma primrec_ctxD : Primrec ctxD := Primrec.succ.comp (Primrec.fst.comp Primrec.snd)

lemma primrec_ctxBCode : Primrec ctxBCode := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

lemma primrec_ctxLive : Primrec ctxLive := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)

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

lemma primrec_decodeOr {α : Type} [Primcodable α] (d : α) : Primrec (decodeOr d) :=
  (Primrec.option_casesOn Primrec.decode (Primrec.const d) Primrec.snd.to₂).of_eq fun n => by
    unfold decodeOr; cases Encodable.decode (α := α) n <;> rfl

lemma decodeOr_encode {α : Type} [Primcodable α] (d a : α) :
    decodeOr d (Encodable.encode a) = a := by
  simp [decodeOr]

lemma unpackCtx_packCtx (c : SymCtx) : unpackCtx (packCtx c) = c := by
  rcases c with ⟨I, Dm1, b, lv⟩
  simp [packCtx, unpackCtx, decodeOr_encode]

lemma primrec_packCtx : Primrec packCtx := by
  have h1 : Primrec fun c : SymCtx => Encodable.encode c.1 :=
    Primrec.encode.comp primrec_ctxI
  have h2 : Primrec fun c : SymCtx => c.2.1 :=
    Primrec.fst.comp Primrec.snd
  have h3 : Primrec fun c : SymCtx => Encodable.encode c.2.2.1 :=
    Primrec.encode.comp primrec_ctxBCode
  have h4 : Primrec fun c : SymCtx => Encodable.encode c.2.2.2 :=
    Primrec.encode.comp primrec_ctxLive
  exact primrec₂_natPair.comp h1 (primrec₂_natPair.comp h2 (primrec₂_natPair.comp h3 h4))

lemma primrec_unpackCtx : Primrec unpackCtx := by
  have u1 : Primrec fun n : ℕ => n.unpair := Primrec.unpair
  have u2 : Primrec fun n : ℕ => n.unpair.2.unpair := Primrec.unpair.comp (Primrec.snd.comp u1)
  have u3 : Primrec fun n : ℕ => n.unpair.2.unpair.2.unpair := Primrec.unpair.comp (Primrec.snd.comp u2)
  exact ((primrec_decodeOr inhInstance).comp (Primrec.fst.comp u1)).pair
    ((Primrec.fst.comp u2).pair
      (((primrec_decodeOr ((0, [], []) : GenDPACode)).comp (Primrec.fst.comp u3)).pair
        ((primrec_decodeOr ([] : List Bool)).comp (Primrec.snd.comp u3))))

lemma primrec_symNextStateOf {α : Type} [Primcodable α] (E : Thm34Engine)
    {c : α → SymCtx} {pos : α → SymPosCode} {act : α → SymActCode}
    {i : α → ℕ} {u : α → List ℕ}
    (hc : Primrec c) (hpos : Primrec pos) (hact : Primrec act)
    (hi : Primrec i) (hu : Primrec u) :
    Primrec fun a => symNextState E (c a) (pos a) (act a) (i a) (u a) := by
  have hp : Primrec fun a =>
      Nat.pair (packCtx (c a))
        (Nat.pair (Encodable.encode (pos a))
          (Nat.pair (Encodable.encode (act a))
            (Nat.pair (i a) (Encodable.encode (u a))))) :=
    primrec₂_natPair.comp (primrec_packCtx.comp hc)
      (primrec₂_natPair.comp (Primrec.encode.comp hpos)
        (primrec₂_natPair.comp (Primrec.encode.comp hact)
          (primrec₂_natPair.comp hi (Primrec.encode.comp hu))))
  exact ((primrec_symNextStatePacked E).comp hp).of_eq fun a => by
    simp only [symNextStatePacked, Nat.unpair_pair,
      unpackCtx_packCtx, decodeOr_encode]

lemma primrec_symComponentsOf {α : Type} [Primcodable α] (E : Thm34Engine)
    {c : α → SymCtx} {pos : α → SymPosCode} {act : α → SymActCode}
    (hc : Primrec c) (hpos : Primrec pos) (hact : Primrec act) :
    Primrec fun a => symComponents E (c a) (pos a) (act a) := by
  have hp : Primrec fun a =>
      Nat.pair (packCtx (c a))
        (Nat.pair (Encodable.encode (pos a)) (Encodable.encode (act a))) :=
    primrec₂_natPair.comp (primrec_packCtx.comp hc)
      (primrec₂_natPair.comp (Primrec.encode.comp hpos) (Primrec.encode.comp hact))
  exact ((primrec_symComponentsPacked E).comp hp).of_eq fun a => by
    simp only [symComponentsPacked, Nat.unpair_pair,
      unpackCtx_packCtx, decodeOr_encode]

def sliceNat (w : List ℕ) (start len : ℕ) : List ℕ :=
  (List.range len).map fun j => w.getD (start + j) 0

lemma primrec_sliceNat : Primrec fun q : List ℕ × (ℕ × ℕ) => sliceNat q.1 q.2.1 q.2.2 := by
  have hfull : Primrec _ :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id)))
      ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst)
        (Primrec.nat_add.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)).to₂
  exact hfull.of_eq fun _ => rfl

lemma sliceNat_eq_take_drop (w : List ℕ) (start len : ℕ) (hle : start + len ≤ w.length) :
    sliceNat w start len = (w.drop start).take len := by
  apply List.ext_getElem
  · simp [sliceNat]; omega
  · intro j hj1 hj2
    have hj_lt : j < len := by simpa [sliceNat] using hj1
    simp only [sliceNat, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
    exact getD_eq_getElem w 0 (start + j) (by omega)

def findHitComps (comps : List (List SymExtElem)) (elem : SymExtElem) : List ℕ :=
  (List.range comps.length).filter fun d =>
    decide (cIdxOf (comps.getD d []) elem < (comps.getD d []).length)

lemma primrec₂_findHitComps : Primrec₂ findHitComps := by
  let R := (List (List SymExtElem) × SymExtElem) × ℕ
  have rc : Primrec fun r : R => r.1.1.getD r.2 [] :=
    (Primrec.list_getD ([] : List SymExtElem)).comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have re : Primrec fun r : R => r.1.2 := Primrec.snd.comp Primrec.fst
  exact filter_primrec (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst))
    (primrec_decide (Primrec.nat_lt.comp (primrec₂_cIdxOf.comp rc re) (Primrec.list_length.comp rc)))

def traceStepNat (E : Thm34Engine) (ctx : SymCtx) (tpσ : ℕ)
    (st : Bool × List ℕ × ℕ) (u : List ℕ) : Bool × List ℕ × ℕ :=
  if st.1 = false then (false, [], 0)
  else
    let addr := st.2.1
    let idx := st.2.2
    let labels := validSymLabels ctx
    let a := (E.unfoldLabelPacked tpσ addr) % (labels.length + 1)
    if a = 0 ∨ labels.length ≤ a - 1 then (false, [], 0)
    else
      let pa := labels.getD (a - 1) (initSymPos, ([], [], []))
      let pos := pa.1
      let act := pa.2
      if pos.1 ≤ idx then (false, [], 0)
      else
        let r := act.1.getD idx 0
        let q' := symNextState E ctx pos act r u
        if (ctxLive ctx).getD q' false = true then
          let comps := symComponents E ctx pos act
          let elem : SymExtElem := (r, u, q')
          let hitComps := findHitComps comps elem
          if hitComps.length = 0 then (false, [], 0)
          else
            let d := hitComps.getD 0 0
            (true, addr ++ [d], cIdxOf (comps.getD d []) elem)
        else (false, [], 0)

lemma primrec_traceStepNatAux (E : Thm34Engine) (cOf : ℕ → SymCtx) (hc0 : Primrec cOf) :
    Primrec fun q : ((ℕ × ℕ) × (Bool × List ℕ × ℕ)) × List ℕ =>
      traceStepNat E (cOf q.1.1.1) q.1.1.2 q.1.2 q.2 := by
  let Q := ((ℕ × ℕ) × (Bool × List ℕ × ℕ)) × List ℕ
  have hctx : Primrec fun q : Q => cOf q.1.1.1 :=
    hc0.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have htpσ : Primrec fun q : Q => q.1.1.2 := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hok : Primrec fun q : Q => q.1.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have haddr : Primrec fun q : Q => q.1.2.2.1 := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hidx : Primrec fun q : Q => q.1.2.2.2 := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hu : Primrec fun q : Q => q.2 := Primrec.snd
  have hlbls := primrec_validSymLabels.comp hctx
  have ha := Primrec.nat_mod.comp (E.primrec₂_unfoldLabelPacked.comp htpσ haddr)
    (Primrec.succ.comp (Primrec.list_length.comp hlbls))
  have hpa := (Primrec.list_getD (initSymPos, ([], [], []))).comp hlbls
    (Primrec.nat_sub.comp ha (Primrec.const 1))
  have hpos := Primrec.fst.comp hpa
  have hact := Primrec.snd.comp hpa
  have hr := (Primrec.list_getD 0).comp (Primrec.fst.comp hact) hidx
  have hq' := primrec_symNextStateOf E hctx hpos hact hr hu
  have hlive := (Primrec.list_getD false).comp (primrec_ctxLive.comp hctx) hq'
  have hcomps := primrec_symComponentsOf E hctx hpos hact
  have helem : Primrec _ := hr.pair (hu.pair hq')
  have hhits : Primrec _ := primrec₂_findHitComps.comp hcomps helem
  have hd := (Primrec.list_getD 0).comp hhits (Primrec.const 0)
  have hcomp_d := (Primrec.list_getD ([] : List SymExtElem)).comp hcomps hd
  have hnew_addr := Primrec.list_append.comp haddr (Primrec.list_cons.comp hd (Primrec.const []))
  have hnew_idx := primrec₂_cIdxOf.comp hcomp_d helem
  have hfail : Primrec fun _ : Q => (false, ([] : List ℕ), 0) := Primrec.const (false, [], 0)
  have hsucc : Primrec _ := (Primrec.const true).pair (hnew_addr.pair hnew_idx)
  exact (Primrec.ite (Primrec.eq.comp hok (Primrec.const false)) hfail
    (Primrec.ite ((Primrec.eq.comp ha (Primrec.const 0)).or
        (Primrec.nat_le.comp (Primrec.list_length.comp hlbls) (Primrec.nat_sub.comp ha (Primrec.const 1))))
      hfail
      (Primrec.ite (Primrec.nat_le.comp (Primrec.fst.comp hpos) hidx) hfail
        (Primrec.ite (Primrec.eq.comp hlive (Primrec.const true))
          (Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp hhits) (Primrec.const 0)) hfail hsucc)
          hfail)))).of_eq fun _ => rfl

lemma primrec_traceStepNatPacked (E : Thm34Engine) :
    Primrec fun q : ((ℕ × ℕ) × (Bool × List ℕ × ℕ)) × List ℕ =>
      traceStepNat E (unpackCtx q.1.1.1) q.1.1.2 q.1.2 q.2 :=
  primrec_traceStepNatAux E unpackCtx primrec_unpackCtx

def traceBlocksNat (E : Thm34Engine) (ctx : SymCtx) (tpσ : ℕ) (wPrefix : List ℕ) :
    Bool × List ℕ × ℕ :=
  let D := ctxD ctx
  let n := wPrefix.length / D
  ((List.range n).map fun m => sliceNat wPrefix (m * D) D).foldl
    (traceStepNat E ctx tpσ) (true, [], 0)

lemma primrec_traceBlocksNat (E : Thm34Engine) :
    Primrec fun q : (SymCtx × ℕ) × List ℕ => traceBlocksNat E q.1.1 q.1.2 q.2 := by
  have hPacked : Primrec fun q : (ℕ × ℕ) × List ℕ =>
      traceBlocksNat E (unpackCtx q.1.1) q.1.2 q.2 := by
    let Q := (ℕ × ℕ) × List ℕ
    have hD : Primrec fun q : Q => ctxD (unpackCtx q.1.1) :=
      primrec_ctxD.comp (primrec_unpackCtx.comp (Primrec.fst.comp Primrec.fst))
    have hn : Primrec fun q : Q => q.2.length / ctxD (unpackCtx q.1.1) :=
      Primrec.nat_div.comp (Primrec.list_length.comp Primrec.snd) hD
    have hblks : Primrec _ := Primrec.list_map (Primrec.list_range.comp hn)
      (primrec_sliceNat.comp
        ((Primrec.snd.comp Primrec.fst).pair
          ((Primrec.nat_mul.comp Primrec.snd (hD.comp Primrec.fst)).pair (hD.comp Primrec.fst)))).to₂
    have hfull : Primrec _ := Primrec.list_foldl hblks (Primrec.const (true, ([] : List ℕ), 0))
      ((primrec_traceStepNatPacked E).comp
        (((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)).pair
          (Primrec.snd.comp Primrec.snd))).to₂
    exact hfull.of_eq fun _ => rfl
  have hpack : Primrec fun q : (SymCtx × ℕ) × List ℕ => ((packCtx q.1.1, q.1.2), q.2) :=
    ((primrec_packCtx.comp (Primrec.fst.comp Primrec.fst)).pair (Primrec.snd.comp Primrec.fst)).pair Primrec.snd
  exact (hPacked.comp hpack).of_eq fun q => by simp [unpackCtx_packCtx]

def evalCandOutNat (E : Thm34Engine) (ctx : SymCtx) (tpσ procTag : ℕ)
    (addr : List ℕ) (idx : ℕ) (wSuf : List ℕ) : ℕ :=
  let I := ctxI ctx
  let D := ctxD ctx
  let labels := validSymLabels ctx
  let words := nonemptyExtWords I D
  let NW := words.length
  let a := (E.unfoldLabelPacked tpσ addr) % (labels.length + 1)
  let pa := labels.getD (a - 1) (initSymPos, ([], [], []))
  let act := pa.2
  let r := act.1.getD idx 0
  let wi := cIdxOf words wSuf
  if procTag = 0 then
    (act.2.1.getD (r * NW + wi) 0) % (I.m1 + 1)
  else
    (act.2.2.getD (r * NW + wi) 0) % (I.m2 + 1)

lemma primrec_evalCandOutNat (E : Thm34Engine) :
    Primrec fun q : ((SymCtx × (ℕ × ℕ)) × (List ℕ × ℕ)) × List ℕ =>
      evalCandOutNat E q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.1.2.1 q.1.2.2 q.2 := by
  let Q := ((SymCtx × (ℕ × ℕ)) × (List ℕ × ℕ)) × List ℕ
  have hctx : Primrec fun q : Q => q.1.1.1 := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have htpσ : Primrec fun q : Q => q.1.1.2.1 := Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hpt : Primrec fun q : Q => q.1.1.2.2 := Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have haddr : Primrec fun q : Q => q.1.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hidx : Primrec fun q : Q => q.1.2.2 := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hwsuf : Primrec fun q : Q => q.2 := Primrec.snd
  have hI := primrec_ctxI.comp hctx
  have hD := primrec_ctxD.comp hctx
  have hlbls := primrec_validSymLabels.comp hctx
  have hwords := primrec₂_nonemptyExtWords.comp hI hD
  have hNW := Primrec.list_length.comp hwords
  have ha := Primrec.nat_mod.comp (E.primrec₂_unfoldLabelPacked.comp htpσ haddr)
    (Primrec.succ.comp (Primrec.list_length.comp hlbls))
  have hpa := (Primrec.list_getD (initSymPos, ([], [], []))).comp hlbls
    (Primrec.nat_sub.comp ha (Primrec.const 1))
  have hact := Primrec.snd.comp hpa
  have hr := (Primrec.list_getD 0).comp (Primrec.fst.comp hact) hidx
  have hwi := primrec₂_cIdxOf.comp hwords hwsuf
  have hflatIdx := Primrec.nat_add.comp (Primrec.nat_mul.comp hr hNW) hwi
  have hb0 := Primrec.nat_mod.comp
    ((Primrec.list_getD 0).comp (Primrec.fst.comp (Primrec.snd.comp hact)) hflatIdx)
    (Primrec.succ.comp (primrec_instM1.comp hI))
  have hb1 := Primrec.nat_mod.comp
    ((Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.snd.comp hact)) hflatIdx)
    (Primrec.succ.comp (primrec_instM2.comp hI))
  exact (Primrec.ite (Primrec.eq.comp hpt (Primrec.const 0)) hb0 hb1).of_eq fun _ => rfl

def evalViewPacked (E : Thm34Engine) (ctx : SymCtx) (qNat : ℕ) : ℕ :=
  let tpσ := qNat.unpair.1
  let procTag := qNat.unpair.2.unpair.1
  let vCode := qNat.unpair.2.unpair.2
  let dep := vdepthNat vCode
  if dep = 0 then 0
  else
    let I := ctxI ctx
    let D := ctxD ctx
    let n := (dep - 1) / D
    let cands := wordsOf (List.range (sigCard I)) dep
    let hits : List ℕ := cands.flatMap fun wFull =>
      let vPair := viewsNatOfCode I wFull
      let vMatch := if procTag = 0 then decide (vPair.1 = vCode) else decide (vPair.2 = vCode)
      if vMatch = true then
        let tr := traceBlocksNat E ctx tpσ (sliceNat wFull 0 (n * D))
        if tr.1 = true then
          [evalCandOutNat E ctx tpσ procTag tr.2.1 tr.2.2 (sliceNat wFull (n * D) (dep - n * D))]
        else []
      else []
    hits.getD 0 0

lemma primrec₂_evalViewPacked (E : Thm34Engine) : Primrec₂ (evalViewPacked E) := by
  let Q := SymCtx × ℕ
  have hctx : Primrec fun q : Q => q.1 := Primrec.fst
  have htpσ : Primrec fun q : Q => q.2.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hpt : Primrec fun q : Q => q.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  have hvC : Primrec fun q : Q => q.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  have hdep := primrec_vdepthNat.comp hvC
  have hI := primrec_ctxI.comp hctx
  have hD := primrec_ctxD.comp hctx
  have hn := Primrec.nat_div.comp (Primrec.nat_sub.comp hdep (Primrec.const 1)) hD
  have hcands := wordsOf_primrec.comp (Primrec.list_range.comp (primrec_sigCard.comp hI)) hdep
  let R := Q × List ℕ
  have rq : Primrec fun r : R => r.1 := Primrec.fst
  have rwFull : Primrec fun r : R => r.2 := Primrec.snd
  have rvPair := primrec₂_viewsNatOfCode.comp (hI.comp rq) rwFull
  have rvMatch : Primrec _ := Primrec.ite (Primrec.eq.comp (hpt.comp rq) (Primrec.const 0))
    (primrec_decide (Primrec.eq.comp (Primrec.fst.comp rvPair) (hvC.comp rq)))
    (primrec_decide (Primrec.eq.comp (Primrec.snd.comp rvPair) (hvC.comp rq)))
  have rnD := Primrec.nat_mul.comp (hn.comp rq) (hD.comp rq)
  have rpre := primrec_sliceNat.comp (rwFull.pair ((Primrec.const 0).pair rnD))
  have rsuf := primrec_sliceNat.comp
    (rwFull.pair (rnD.pair (Primrec.nat_sub.comp (hdep.comp rq) rnD)))
  have rtr := (primrec_traceBlocksNat E).comp (((hctx.comp rq).pair (htpσ.comp rq)).pair rpre)
  have rout := (primrec_evalCandOutNat E).comp
    (((((hctx.comp rq).pair ((htpσ.comp rq).pair (hpt.comp rq))).pair
        ((Primrec.fst.comp (Primrec.snd.comp rtr)).pair
          (Primrec.snd.comp (Primrec.snd.comp rtr)))).pair rsuf))
  have rcell : Primrec _ := Primrec.ite (Primrec.eq.comp rvMatch (Primrec.const true))
    (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp rtr) (Primrec.const true))
      (Primrec.list_cons.comp rout (Primrec.const []))
      (Primrec.const []))
    (Primrec.const [])
  have hhits : Primrec _ := Primrec.list_flatMap hcands rcell.to₂
  have hfull : Primrec _ := Primrec.ite (Primrec.eq.comp hdep (Primrec.const 0))
    (Primrec.const 0)
    ((Primrec.list_getD 0).comp hhits (Primrec.const 0))
  exact hfull.of_eq fun _ => rfl

lemma evalCandOutNat_lt (E : Thm34Engine) (ctx : SymCtx) (tpσ : ℕ)
    (addr : List ℕ) (idx : ℕ) (wSuf : List ℕ) :
    evalCandOutNat E ctx tpσ 0 addr idx wSuf < (ctxI ctx).m1 + 1 ∧
      evalCandOutNat E ctx tpσ 1 addr idx wSuf < (ctxI ctx).m2 + 1 := by
  unfold evalCandOutNat
  exact ⟨Nat.mod_lt _ (Nat.succ_pos _), Nat.mod_lt _ (Nat.succ_pos _)⟩

lemma evalViewPacked_lt (E : Thm34Engine) (ctx : SymCtx) (tpσ vCode : ℕ) :
    evalViewPacked E ctx (Nat.pair tpσ (Nat.pair 0 vCode)) < (ctxI ctx).m1 + 1 ∧
      evalViewPacked E ctx (Nat.pair tpσ (Nat.pair 1 vCode)) < (ctxI ctx).m2 + 1 := by
  let dep := vdepthNat vCode
  let I := ctxI ctx
  let D := ctxD ctx
  let n := (dep - 1) / D
  let hits0 : List ℕ := (wordsOf (List.range (sigCard I)) dep).flatMap fun wFull =>
    let vPair := viewsNatOfCode I wFull
    if decide (vPair.1 = vCode) = true then
      let tr := traceBlocksNat E ctx tpσ (sliceNat wFull 0 (n * D))
      if tr.1 = true then
        [evalCandOutNat E ctx tpσ 0 tr.2.1 tr.2.2 (sliceNat wFull (n * D) (dep - n * D))]
      else []
    else []
  let hits1 : List ℕ := (wordsOf (List.range (sigCard I)) dep).flatMap fun wFull =>
    let vPair := viewsNatOfCode I wFull
    if decide (vPair.2 = vCode) = true then
      let tr := traceBlocksNat E ctx tpσ (sliceNat wFull 0 (n * D))
      if tr.1 = true then
        [evalCandOutNat E ctx tpσ 1 tr.2.1 tr.2.2 (sliceNat wFull (n * D) (dep - n * D))]
      else []
    else []
  have h0 : ∀ x ∈ hits0, x < (ctxI ctx).m1 + 1 := by
    intro x hx
    simp only [hits0, List.mem_flatMap] at hx
    rcases hx with ⟨wFull, _, hm⟩
    split_ifs at hm <;> simp only [List.mem_singleton, List.not_mem_nil] at hm
    subst hm
    exact (evalCandOutNat_lt E ctx tpσ _ _ _).1
  have h1 : ∀ x ∈ hits1, x < (ctxI ctx).m2 + 1 := by
    intro x hx
    simp only [hits1, List.mem_flatMap] at hx
    rcases hx with ⟨wFull, _, hm⟩
    split_ifs at hm <;> simp only [List.mem_singleton, List.not_mem_nil] at hm
    subst hm
    exact (evalCandOutNat_lt E ctx tpσ _ _ _).2
  unfold evalViewPacked
  simp only [Nat.unpair_pair, ↓reduceIte, one_ne_zero]
  by_cases hd : dep = 0
  · simp [dep] at hd; simp [hd]
  · have hd' : vdepthNat vCode ≠ 0 := hd
    rw [if_neg hd', if_neg hd']
    change hits0.getD 0 0 < (ctxI ctx).m1 + 1 ∧ hits1.getD 0 0 < (ctxI ctx).m2 + 1
    constructor
    · by_cases hl0 : 0 < hits0.length
      · rw [getD_eq_getElem hits0 0 0 hl0]
        exact h0 _ (List.getElem_mem hl0)
      · rw [getD_of_ge hits0 0 0 (by omega)]; exact Nat.succ_pos _
    · by_cases hl1 : 0 < hits1.length
      · rw [getD_eq_getElem hits1 0 0 hl1]
        exact h1 _ (List.getElem_mem hl1)
      · rw [getD_of_ge hits1 0 0 (by omega)]; exact Nat.succ_pos _

def foldBlocksNat (E : Thm34Engine) (ctx : SymCtx) (tpσ : ℕ) (us : List (List ℕ)) :
    Bool × List ℕ × ℕ :=
  us.foldl (traceStepNat E ctx tpσ) (true, [], 0)

lemma foldBlocksNat_snoc (E : Thm34Engine) (ctx : SymCtx) (tpσ : ℕ)
    (xs : List (List ℕ)) (u : List ℕ) :
    foldBlocksNat E ctx tpσ (xs ++ [u]) = traceStepNat E ctx tpσ (foldBlocksNat E ctx tpσ xs) u := by
  simp only [foldBlocksNat, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma traceBlocksNat_eq_foldBlocksNat (E : Thm34Engine)
    (I : Instance) (D_m1 D : ℕ) (hD_def : D = D_m1 + 1)
    (bCode : GenDPACode) (liveList : List Bool)
    (ctx : SymCtx) (hctx_def : ctx = (I, D_m1, bCode, liveList))
    (tpσ m : ℕ) (wPre : List ℕ) (hlen : wPre.length = m * D) :
    traceBlocksNat E ctx tpσ wPre =
      foldBlocksNat E ctx tpσ ((List.range m).map fun k => (wPre.drop (k * D)).take D) := by
  subst hD_def
  subst hctx_def
  let D := D_m1 + 1
  have hD_pos : 0 < D := Nat.succ_pos D_m1
  unfold traceBlocksNat foldBlocksNat
  have hdiv : wPre.length / D = m := by
    rw [hlen, Nat.mul_div_cancel _ hD_pos]
  dsimp only [ctxD]
  rw [hdiv]
  congr 1
  apply List.map_congr_left
  intro k hk
  have hk_lt : k < m := List.mem_range.mp hk
  have hle : k * D + D ≤ wPre.length := by
    rw [hlen]
    have h1 : k + 1 ≤ m := hk_lt
    calc k * D + D = (k + 1) * D := (Nat.succ_mul k D).symm
      _ ≤ m * D := Nat.mul_le_mul_right D h1
  exact sliceNat_eq_take_drop wPre (k * D) D hle

lemma foldBlocksNat_valid (E : Thm34Engine)
    (I : Instance) (D_m1 D : ℕ) (_hD_def : D = D_m1 + 1)
    (bCode : GenDPACode) (liveList : List Bool)
    (ctx : SymCtx) (_hctx_def : ctx = (I, D_m1, bCode, liveList))
    (ts : TreeSpecCode) (hts_def : ts = buildTreeSpec E ctx)
    (σ : List ℕ) (hsol : E.solveTreePG ts = some σ)
    (tpσ : ℕ) (htpσ_def : tpσ = Nat.pair (E.packTS ts) (Encodable.encode σ))
    (tTree : List (Fin (ts.1 + 1)) → Fin (ts.2.1 + 1))
    (htTree_def : tTree = fun addr =>
      ⟨(E.unfoldLabelPacked tpσ (addr.map Fin.val)) % (ts.2.1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩)
    (labels : List (SymPosCode × SymActCode))
    (hlabels_def : labels = validSymLabels ctx) :
    ∀ (us : List (List ℕ)),
      (∀ u ∈ us, u ∈ fullBlocks I D) →
      ∀ addr idx, foldBlocksNat E ctx tpσ us = (true, addr, idx) →
        ∃ addrFin : List (Fin (ts.1 + 1)),
          addr = addrFin.map Fin.val ∧ addrFin.length = us.length ∧
          (tTree addrFin).val ≠ 0 ∧ (tTree addrFin).val - 1 < labels.length ∧
          labels.getD ((tTree addrFin).val - 1) (initSymPos, ([], [], [])) ∈ labels ∧
          idx < (labels.getD ((tTree addrFin).val - 1) (initSymPos, ([], [], []))).1.1 := by
  have hts_len : ts.2.1 = labels.length := by rw [hts_def, hlabels_def]; rfl
  let B_full := ctxBFull ctx
  have hB_succ : ts.1 + 1 = B_full := by rw [hts_def]; exact Nat.sub_add_cancel (ctxBFull_pos ctx)
  have hvat : ValidAcceptingTree ts tTree := by
    subst hts_def htpσ_def htTree_def
    exact E.solveTreePG_some_sound _ σ hsol
  obtain ⟨hroot_ok, hchild_ok, _⟩ := hvat
  have hroot_eq : ∀ a : Fin (ts.2.1 + 1),
      tsRootOk ts a = (if a.val = 0 then false
        else decide ((labels.getD (a.val - 1) (initSymPos, ([], [], []))).1 = initSymPos)) := by
    intro a; subst hts_def; rw [tsRootOk_buildTreeSpec, ← hlabels_def]
  have hchild_eq : ∀ (a : Fin (ts.2.1 + 1)) (d0 : Fin (ts.1 + 1)) (a' : Fin (ts.2.1 + 1)),
      tsChildOk ts a d0 a' =
        (if a.val = 0 then decide (a'.val = 0)
         else
           let pa := labels.getD (a.val - 1) (initSymPos, ([], [], []))
           let comps := symComponents E ctx pa.1 pa.2
           if d0.val < comps.length then
             if a'.val = 0 then false
             else
               let pa' := labels.getD (a'.val - 1) (initSymPos, ([], [], []))
               decide (pa'.1 = childSymPos (ctxI ctx) pa.1 (comps.getD d0.val []))
           else decide (a'.val = 0)) := by
    intro a d0 a'; subst hts_def; rw [tsChildOk_buildTreeSpec, ← hlabels_def]
  intro us
  induction us using List.reverseRecOn with
  | nil =>
    intro _ addr idx h0
    simp only [foldBlocksNat, List.foldl_nil, Prod.mk.injEq] at h0
    rcases h0 with ⟨_, ⟨rfl, rfl⟩⟩
    refine ⟨[], rfl, rfl, ?_⟩
    rw [hroot_eq] at hroot_ok
    by_cases ha0 : (tTree []).val = 0
    · rw [if_pos ha0] at hroot_ok; cases hroot_ok
    · rw [if_neg ha0] at hroot_ok
      have ha_lt : (tTree []).val - 1 < labels.length := by
        have := (tTree []).isLt; omega
      rw [getD_eq_getElem labels _ _ ha_lt, decide_eq_true_eq] at hroot_ok
      refine ⟨ha0, ha_lt, ?_, ?_⟩
      · rw [getD_eq_getElem labels _ _ ha_lt]
        exact List.getElem_mem ha_lt
      · rw [getD_eq_getElem labels _ _ ha_lt, hroot_ok]
        exact Nat.one_pos
  | append_singleton us u ih =>
    intro hus addr' idx' h1
    rw [foldBlocksNat_snoc] at h1
    rcases hprev : foldBlocksNat E ctx tpσ us with ⟨prev_ok, prev_addr, prev_idx⟩
    rw [hprev] at h1
    cases prev_ok with
    | false =>
      simp [traceStepNat] at h1
    | true =>
      obtain ⟨addrFin, haddr_eq, haddr_len, ha_ne, ha_lt, hpa_mem, hidx_lt⟩ :=
        ih (fun x hx => hus x (List.mem_append_left _ hx)) prev_addr prev_idx hprev
      rw [getD_eq_getElem labels _ _ ha_lt] at hpa_mem hidx_lt
      unfold traceStepNat at h1
      rw [← hlabels_def] at h1
      dsimp only at h1
      have ha_val : (E.unfoldLabelPacked tpσ prev_addr) % (labels.length + 1) = (tTree addrFin).val := by
        rw [htTree_def]; dsimp only; rw [haddr_eq, hts_len]
      rw [if_neg (by decide), ha_val, if_neg (by omega), getD_eq_getElem labels _ _ ha_lt] at h1
      rw [if_neg (by omega)] at h1
      let pa := labels[(tTree addrFin).val - 1]'ha_lt
      let r := pa.2.1.getD prev_idx 0
      let q' := symNextState E ctx pa.1 pa.2 r u
      let comps := symComponents E ctx pa.1 pa.2
      let elem : SymExtElem := (r, u, q')
      let hitComps := findHitComps comps elem
      change (if (ctxLive ctx).getD q' false = true then
        if hitComps.length = 0 then (false, [], 0)
        else (true, prev_addr ++ [hitComps.getD 0 0],
          cIdxOf (comps.getD (hitComps.getD 0 0) []) elem)
      else (false, [], 0)) = (true, addr', idx') at h1
      by_cases hlive : (ctxLive ctx).getD q' false = true
      · rw [if_pos hlive] at h1
        by_cases hlen_hits : hitComps.length = 0
        · rw [if_pos hlen_hits] at h1; cases h1
        · rw [if_neg hlen_hits] at h1
          let d := hitComps.getD 0 0
          rcases Prod.mk.inj h1 with ⟨_, h1'⟩
          rcases Prod.mk.inj h1' with ⟨haddr'_eq, hidx'_eq⟩
          have hd_mem : d ∈ hitComps := by
            dsimp only [d]; rw [getD_eq_getElem hitComps 0 0 (by omega)]
            exact List.getElem_mem (by omega)
          have hd_mem' : d < comps.length ∧ cIdxOf (comps.getD d []) elem < (comps.getD d []).length := by
            simpa only [hitComps, findHitComps, List.mem_filter, List.mem_range, decide_eq_true_eq] using hd_mem
          have hd_lt_comps : d < comps.length := hd_mem'.1
          have hpa_mem' : pa ∈ validSymLabels ctx := hlabels_def ▸ hpa_mem
          have hact_ok := ((mem_validSymLabels_iff ctx pa).mp hpa_mem').2.2
          unfold actValid at hact_ok
          rw [decide_eq_true_eq] at hact_ok
          have hcomps_le : comps.length ≤ B_full :=
            (symComponents_props E ctx pa.1 pa.2 hact_ok.2.1).1
          have hd_lt_ts : d < ts.1 + 1 := by rw [hB_succ]; exact lt_of_lt_of_le hd_lt_comps hcomps_le
          let dFin : Fin (ts.1 + 1) := ⟨d, hd_lt_ts⟩
          have hFin_d : dFin.val = d := by dsimp only [dFin]
          have hch_ok := hchild_ok addrFin dFin
          rw [hchild_eq, if_neg ha_ne,
            getD_eq_getElem labels _ _ ha_lt, hFin_d] at hch_ok
          dsimp only at hch_ok
          rw [if_pos hd_lt_comps] at hch_ok
          by_cases ha'_zero : (tTree (addrFin ++ [dFin])).val = 0
          · rw [if_pos ha'_zero] at hch_ok; cases hch_ok
          · rw [if_neg ha'_zero] at hch_ok
            have ha'_lt : (tTree (addrFin ++ [dFin])).val - 1 < labels.length := by
              have := (tTree (addrFin ++ [dFin])).isLt; omega
            rw [getD_eq_getElem labels _ _ ha'_lt, decide_eq_true_eq] at hch_ok
            have hch_ok' : labels[(tTree (addrFin ++ [dFin])).val - 1].1 =
                childSymPos (ctxI ctx) pa.1 (comps.getD d []) := by
              dsimp only [pa, comps]; exact hch_ok
            refine ⟨addrFin ++ [dFin],
              by rw [← haddr'_eq, haddr_eq, List.map_append, List.map_singleton, hFin_d],
              by rw [List.length_append, List.length_append, List.length_singleton,
                List.length_singleton, haddr_len],
              ha'_zero, ha'_lt, ?_, ?_⟩
            · rw [getD_eq_getElem labels _ _ ha'_lt]
              exact List.getElem_mem ha'_lt
            · rw [getD_eq_getElem labels _ _ ha'_lt, ← hidx'_eq, hch_ok']
              dsimp only [childSymPos]
              exact hd_mem'.2
      · rw [if_neg hlive] at h1; cases h1

lemma symComponents_same_hit (E : Thm34Engine) (ctx : SymCtx) (pa : SymPosCode × SymActCode)
    (hfix_le : (fixedIdxs pa.1 pa.2).length ≤ ctxBRed ctx)
    (elem1 elem2 : SymExtElem)
    (he1_S : elem1 ∈ symLiveExts E ctx pa.1 pa.2)
    (he2_S : elem2 ∈ symLiveExts E ctx pa.1 pa.2)
    (hadj12 : symExtAdj (ctxI ctx) pa.1 elem1 elem2 = true)
    (hadj21 : symExtAdj (ctxI ctx) pa.1 elem2 elem1 = true) :
    ∀ d < (symComponents E ctx pa.1 pa.2).length,
      (cIdxOf ((symComponents E ctx pa.1 pa.2).getD d []) elem1 <
        ((symComponents E ctx pa.1 pa.2).getD d []).length) ↔
      (cIdxOf ((symComponents E ctx pa.1 pa.2).getD d []) elem2 <
        ((symComponents E ctx pa.1 pa.2).getD d []).length) := by
  let S := symLiveExts E ctx pa.1 pa.2
  let comps := symComponents E ctx pa.1 pa.2
  let I := ctxI ctx
  have hS_nd : S.Nodup := (symLiveExts_nodup_and_length E ctx pa.1 pa.2 hfix_le).1
  have hs1_sp := cIdxOf_lt_and_getElem he1_S
  have hs1_lt := hs1_sp.1
  have hs1_get := hs1_sp.2
  have hs2_sp := cIdxOf_lt_and_getElem he2_S
  have hs2_lt := hs2_sp.1
  have hs2_get := hs2_sp.2
  let s1 := cIdxOf S elem1
  let s2 := cIdxOf S elem2
  intro d hd
  rw [cIdxOf_lt_iff_mem, cIdxOf_lt_iff_mem, getD_eq_getElem comps [] d hd]
  have hd_ci : d < (componentsIdx inhSymExt S (symExtAdj I pa.1)).length := by
    simpa [comps, symComponents, I] using hd
  let idxs := (componentsIdx inhSymExt S (symExtAdj I pa.1))[d]'hd_ci
  have hcomp_d : comps[d]'hd = idxs.map (fun idx => S.getD idx inhSymExt) := by
    simp [comps, symComponents, idxs, S, I]
  have hidxs_mem : idxs ∈ componentsIdx inhSymExt S (symExtAdj I pa.1) :=
    List.getElem_mem hd_ci
  rw [componentsIdx, mem_dedupList, List.mem_map] at hidxs_mem
  rcases hidxs_mem with ⟨i0, hi0_r, hidxs_eq⟩
  have hi0_lt : i0 < S.length := List.mem_range.mp hi0_r
  have hall_lt := (compIdxOf_nodup_and_lt inhSymExt S (symExtAdj I pa.1) hi0_lt).2.2.2
  rw [hidxs_eq] at hall_lt
  have hmem_iff : ∀ (el : SymExtElem) (s : ℕ) (hs : s < S.length),
      S[s]'hs = el → (el ∈ comps[d]'hd ↔ s ∈ idxs) := by
    intro el s hs hget
    rw [hcomp_d, List.mem_map]
    constructor
    · rintro ⟨idx, hidx, heq⟩
      have hidx_lt := hall_lt idx hidx
      rw [getD_eq_getElem S inhSymExt idx hidx_lt, ← hget] at heq
      have his : idx = s := (List.Nodup.getElem_inj_iff hS_nd).mp heq
      rwa [← his]
    · intro hs_in
      refine ⟨s, hs_in, ?_⟩
      rw [getD_eq_getElem S inhSymExt s hs, hget]
  rw [hmem_iff elem1 s1 hs1_lt hs1_get, hmem_iff elem2 s2 hs2_lt hs2_get,
    ← hidxs_eq, mem_compIdxOf_iff inhSymExt S _ hi0_lt s1,
    mem_compIdxOf_iff inhSymExt S _ hi0_lt s2]
  have hstep12 : s1 < S.length ∧ s2 < S.length ∧
      symExtAdj I pa.1 (S.getD s1 inhSymExt) (S.getD s2 inhSymExt) = true := by
    refine ⟨hs1_lt, hs2_lt, ?_⟩
    rw [getD_eq_getElem S inhSymExt s1 hs1_lt, getD_eq_getElem S inhSymExt s2 hs2_lt,
      hs1_get, hs2_get]
    exact hadj12
  have hstep21 : s2 < S.length ∧ s1 < S.length ∧
      symExtAdj I pa.1 (S.getD s2 inhSymExt) (S.getD s1 inhSymExt) = true := by
    refine ⟨hs2_lt, hs1_lt, ?_⟩
    rw [getD_eq_getElem S inhSymExt s2 hs2_lt, getD_eq_getElem S inhSymExt s1 hs1_lt,
      hs2_get, hs1_get]
    exact hadj21
  exact ⟨fun ⟨_, hr⟩ => ⟨hs2_lt, hr.tail hstep12⟩,
    fun ⟨_, hr⟩ => ⟨hs1_lt, hr.tail hstep21⟩⟩

lemma foldBlocksNat_hom (E : Thm34Engine)
    (I : Instance) (D_m1 D : ℕ) (hD_def : D = D_m1 + 1)
    (bCode : GenDPACode) (liveList : List Bool)
    (ctx : SymCtx) (hctx_def : ctx = (I, D_m1, bCode, liveList))
    (ts : TreeSpecCode) (hts_def : ts = buildTreeSpec E ctx)
    (σ : List ℕ) (hsol : E.solveTreePG ts = some σ)
    (tpσ : ℕ) (htpσ_def : tpσ = Nat.pair (E.packTS ts) (Encodable.encode σ))
    (labels : List (SymPosCode × SymActCode))
    (hlabels_def : labels = validSymLabels ctx) :
    ∀ (us1 us2 : List (List ℕ)),
      us1.length = us2.length →
      (∀ u ∈ us1, u ∈ fullBlocks I D) →
      (∀ u ∈ us2, u ∈ fullBlocks I D) →
      ∀ addr1 idx1 addr2 idx2,
        foldBlocksNat E ctx tpσ us1 = (true, addr1, idx1) →
        foldBlocksNat E ctx tpσ us2 = (true, addr2, idx2) →
        EdgeAdj (decHist I (us1.flatten)) (decHist I (us2.flatten)) →
        addr1 = addr2 ∧
        let a := (E.unfoldLabelPacked tpσ addr1) % (labels.length + 1)
        let pos := (labels.getD (a - 1) (initSymPos, ([], [], []))).1
        (view1 (decHist I us1.flatten) = view1 (decHist I us2.flatten) → eq1At pos idx1 idx2 = true) ∧
        (view2 (decHist I us1.flatten) = view2 (decHist I us2.flatten) → eq2At pos idx1 idx2 = true) := by
  subst hD_def
  subst hctx_def
  subst hts_def
  subst htpσ_def
  let D := D_m1 + 1
  let ctx : SymCtx := (I, D_m1, bCode, liveList)
  let ts := buildTreeSpec E ctx
  let tpσ := Nat.pair (E.packTS ts) (Encodable.encode σ)
  have hts_len : ts.2.1 = labels.length := by rw [hlabels_def]; rfl
  let B_full := ctxBFull ctx
  have hB_succ : ts.1 + 1 = B_full := Nat.sub_add_cancel (ctxBFull_pos ctx)
  let tTree : List (Fin (ts.1 + 1)) → Fin (ts.2.1 + 1) := fun addr =>
    ⟨(E.unfoldLabelPacked tpσ (addr.map Fin.val)) % (ts.2.1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  have hvat : ValidAcceptingTree ts tTree := E.solveTreePG_some_sound ts σ hsol
  obtain ⟨hroot_ok, hchild_ok, _⟩ := hvat
  have hfold_valid := foldBlocksNat_valid E I D_m1 D rfl bCode liveList ctx rfl ts rfl σ hsol tpσ rfl
    tTree rfl labels hlabels_def
  suffices haux : ∀ (m : ℕ) (us1 us2 : List (List ℕ)),
      us1.length = m → us2.length = m →
      (∀ u ∈ us1, u ∈ fullBlocks I D) →
      (∀ u ∈ us2, u ∈ fullBlocks I D) →
      ∀ addr1 idx1 addr2 idx2,
        foldBlocksNat E ctx tpσ us1 = (true, addr1, idx1) →
        foldBlocksNat E ctx tpσ us2 = (true, addr2, idx2) →
        EdgeAdj (decHist I (us1.flatten)) (decHist I (us2.flatten)) →
        addr1 = addr2 ∧
        let a := (E.unfoldLabelPacked tpσ addr1) % (labels.length + 1)
        let pos := (labels.getD (a - 1) (initSymPos, ([], [], []))).1
        (view1 (decHist I us1.flatten) = view1 (decHist I us2.flatten) → eq1At pos idx1 idx2 = true) ∧
        (view2 (decHist I us1.flatten) = view2 (decHist I us2.flatten) → eq2At pos idx1 idx2 = true) from
    fun us1 us2 hlen => haux us1.length us1 us2 rfl hlen.symm
  intro m
  induction m with
    | zero =>
      intro us1 us2 hl1 hl2 _ _ addr1 idx1 addr2 idx2 h1 h2 _
      cases List.eq_nil_of_length_eq_zero hl1
      cases List.eq_nil_of_length_eq_zero hl2
      simp only [foldBlocksNat, List.foldl_nil, Prod.mk.injEq] at h1 h2
      rcases h1 with ⟨_, ⟨rfl, rfl⟩⟩
      rcases h2 with ⟨_, ⟨rfl, rfl⟩⟩
      refine ⟨rfl, ?_⟩
      rw [tsRootOk_buildTreeSpec, ← hlabels_def] at hroot_ok
      by_cases ha0 : (tTree []).val = 0
      · rw [if_pos ha0] at hroot_ok; cases hroot_ok
      · rw [if_neg ha0, decide_eq_true_eq] at hroot_ok
        dsimp only
        have ha_eq : (E.unfoldLabelPacked tpσ []) % (labels.length + 1) = (tTree []).val := by
          dsimp only [tTree]; rw [List.map_nil, hts_len]
        rw [ha_eq, hroot_ok]
        exact ⟨fun _ => rfl, fun _ => rfl⟩
    | succ m ih =>
      intro us1 us2 hl1 hl2 hus1 hus2 addr1' idx1' addr2' idx2' h1 h2 hadj_ext
      cases us1 using List.reverseRecOn with
      | nil => simp at hl1
      | append_singleton us1 u1 =>
        cases us2 using List.reverseRecOn with
        | nil => simp at hl2
        | append_singleton us2 u2 =>
          have hlen1 : us1.length = m := by simpa using hl1
          have hlen2 : us2.length = m := by simpa using hl2
          have hlen' : us1.length = us2.length := hlen1.trans hlen2.symm
          have hu1_blk : u1 ∈ fullBlocks I D := hus1 u1 (List.mem_append_right _ (List.mem_singleton.mpr rfl))
          have hu2_blk : u2 ∈ fullBlocks I D := hus2 u2 (List.mem_append_right _ (List.mem_singleton.mpr rfl))
          have hus1' : ∀ u ∈ us1, u ∈ fullBlocks I D := fun u hu => hus1 u (List.mem_append_left _ hu)
          have hus2' : ∀ u ∈ us2, u ∈ fullBlocks I D := fun u hu => hus2 u (List.mem_append_left _ hu)
          have hflat_len : ∀ (xs : List (List ℕ)), (∀ u ∈ xs, u ∈ fullBlocks I D) →
              (decHist I xs.flatten).length = xs.length * D := by
            intro xs hxs
            rw [decHist, List.length_map]
            induction xs with
            | nil => simp
            | cons x xtl ihx =>
              have hx_len := ((mem_fullBlocks_iff I D x).mp (hxs x (List.mem_cons.mpr (Or.inl rfl)))).1
              simp only [List.flatten_cons, List.length_append, hx_len, List.length_cons,
                ihx (fun y hy => hxs y (List.mem_cons_of_mem _ hy))]
              ring
          have hlen_h12 : (decHist I us1.flatten).length = (decHist I us2.flatten).length := by
            rw [hflat_len us1 hus1', hflat_len us2 hus2', hlen']
          have hdec_split1 : decHist I (us1 ++ [u1]).flatten = decHist I us1.flatten ++ decHist I u1 := by
            simp [decHist]
          have hdec_split2 : decHist I (us2 ++ [u2]).flatten = decHist I us2.flatten ++ decHist I u2 := by
            simp [decHist]
          rw [hdec_split1, hdec_split2] at hadj_ext ⊢
          have hadj_pre : EdgeAdj (decHist I us1.flatten) (decHist I us2.flatten) := by
            rcases hadj_ext with hv1 | hv2
            · exact Or.inl (viewOf_prefix_eq (p := .one) hlen_h12 hv1).2
            · exact Or.inr (viewOf_prefix_eq (p := .two) hlen_h12 hv2).2
          -- Unpack previous fold states for both `us1` and `us2`
          rw [foldBlocksNat_snoc] at h1 h2
          rcases hf1 : foldBlocksNat E ctx tpσ us1 with ⟨b1, addr1, idx1⟩
          rcases hf2 : foldBlocksNat E ctx tpσ us2 with ⟨b2, addr2, idx2⟩
          rw [hf1] at h1
          rw [hf2] at h2
          cases b1 with
          | false => simp [traceStepNat] at h1
          | true =>
            cases b2 with
            | false => simp [traceStepNat] at h2
            | true =>
              have hih12 := ih us1 us2 hlen1 hlen2 hus1' hus2' addr1 idx1 addr2 idx2 hf1 hf2 hadj_pre
              rcases hih12 with ⟨haddr12, hhom12⟩
              have hih21 := ih us2 us1 hlen2 hlen1 hus2' hus1' addr2 idx2 addr1 idx1 hf2 hf1
                (hadj_pre.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm))
              have hhom21 := hih21.2
              subst haddr12
              have hfv1 := hfold_valid us1 hus1' addr1 idx1 hf1
              rcases hfv1 with ⟨addrFin, haddr_fin, _, ha_ne, ha_lt, hpa_mem, hidx1_lt⟩
              have hfv2 := hfold_valid us2 hus2' addr1 idx2 hf2
              rcases hfv2 with ⟨addrFin2, haddr_fin2, _, _, _, _, hidx2_lt⟩
              have hw_eq : addrFin2 = addrFin :=
                List.map_injective_iff.mpr Fin.val_injective (haddr_fin2.symm.trans haddr_fin)
              rw [hw_eq] at hidx2_lt
              dsimp only at hhom12 hhom21
              rw [getD_eq_getElem labels _ _ ha_lt] at hpa_mem hidx1_lt hidx2_lt
              let pa := labels[(tTree addrFin).val - 1]'ha_lt
              have ha_eq : (E.unfoldLabelPacked tpσ addr1) % (labels.length + 1) = (tTree addrFin).val := by
                dsimp only [tTree]; rw [haddr_fin, hts_len]
              have hpa_get : labels.getD ((E.unfoldLabelPacked tpσ addr1) % (labels.length + 1) - 1)
                  (initSymPos, ([], [], [])) = pa := by
                rw [ha_eq, getD_eq_getElem labels _ _ ha_lt]
              rw [hpa_get] at hhom12 hhom21
              have hpa_mem' : pa ∈ validSymLabels ctx := hlabels_def ▸ hpa_mem
              have hact_valid := ((mem_validSymLabels_iff ctx pa).mp hpa_mem').2.2
              unfold actValid at hact_valid
              rw [decide_eq_true_eq] at hact_valid
              obtain ⟨hr_idem, hfix_le, _, hr_vw, _⟩ := hact_valid
              have hact_mem := ((mem_validSymLabels_iff ctx pa).mp hpa_mem').2.1
              rw [mem_allSymActsFor_iff] at hact_mem
              let r1 := pa.2.1.getD idx1 0
              let r2 := pa.2.1.getD idx2 0
              have hr1_lt : r1 < pa.1.1 := by
                dsimp [r1]
                rw [getD_eq_getElem pa.2.1 0 idx1 (hact_mem.1 ▸ hidx1_lt)]
                exact hact_mem.2.1 _ (List.getElem_mem _)
              have hr2_lt : r2 < pa.1.1 := by
                dsimp [r2]
                rw [getD_eq_getElem pa.2.1 0 idx2 (hact_mem.1 ▸ hidx2_lt)]
                exact hact_mem.2.1 _ (List.getElem_mem _)
              have hr12 : (view1 (decHist I us1.flatten) = view1 (decHist I us2.flatten) → eq1At pa.1 r1 r2 = true) ∧
                  (view2 (decHist I us1.flatten) = view2 (decHist I us2.flatten) → eq2At pa.1 r1 r2 = true) := by
                dsimp only [r1, r2]
                exact ⟨fun hv => (hr_vw idx1 hidx1_lt idx2 hidx2_lt).1 (hhom12.1 hv),
                  fun hv => (hr_vw idx1 hidx1_lt idx2 hidx2_lt).2 (hhom12.2 hv)⟩
              have hr21 : (view1 (decHist I us2.flatten) = view1 (decHist I us1.flatten) → eq1At pa.1 r2 r1 = true) ∧
                  (view2 (decHist I us2.flatten) = view2 (decHist I us1.flatten) → eq2At pa.1 r2 r1 = true) := by
                dsimp only [r1, r2]
                exact ⟨fun hv => (hr_vw idx2 hidx2_lt idx1 hidx1_lt).1 (hhom21.1 hv),
                  fun hv => (hr_vw idx2 hidx2_lt idx1 hidx1_lt).2 (hhom21.2 hv)⟩
              have hext12 := extEqFrom_of_hom I hlen_h12 hr12.1 hr12.2 u1 u2
              have hext21 := extEqFrom_of_hom I hlen_h12.symm hr21.1 hr21.2 u2 u1
              -- Unpack `traceStepNat` for both `h1` and `h2`
              unfold traceStepNat at h1 h2
              rw [← hlabels_def] at h1 h2
              dsimp only at h1 h2
              rw [if_neg (by decide), ha_eq, if_neg (by omega), getD_eq_getElem labels _ _ ha_lt] at h1 h2
              rw [if_neg (by omega)] at h1
              rw [if_neg (by omega)] at h2
              let q1' := symNextState E ctx pa.1 pa.2 r1 u1
              let q2' := symNextState E ctx pa.1 pa.2 r2 u2
              by_cases hl1 : (ctxLive ctx).getD q1' false = true
              · rw [if_pos hl1] at h1
                by_cases hl2 : (ctxLive ctx).getD q2' false = true
                · rw [if_pos hl2] at h2
                  let S := symLiveExts E ctx pa.1 pa.2
                  let comps := symComponents E ctx pa.1 pa.2
                  let elem1 : SymExtElem := (r1, u1, q1')
                  let elem2 : SymExtElem := (r2, u2, q2')
                  let hits1 := findHitComps comps elem1
                  let hits2 := findHitComps comps elem2
                  have h1_s : (if hits1.length = 0 then (false, [], 0)
                    else (true, addr1 ++ [hits1.getD 0 0],
                      cIdxOf (comps.getD (hits1.getD 0 0) []) elem1)) = (true, addr1', idx1') := by
                    dsimp only [pa, comps, elem1, hits1, q1', r1]; exact h1
                  have h2_s : (if hits2.length = 0 then (false, [], 0)
                    else (true, addr1 ++ [hits2.getD 0 0],
                      cIdxOf (comps.getD (hits2.getD 0 0) []) elem2)) = (true, addr2', idx2') := by
                    dsimp only [pa, comps, elem2, hits2, q2', r2]; exact h2
                  have hr1_fix : r1 ∈ fixedIdxs pa.1 pa.2 := by
                    simp only [fixedIdxs, List.mem_filter, List.mem_range, decide_eq_true_eq]
                    exact ⟨hr1_lt, hr_idem idx1 hidx1_lt⟩
                  have hr2_fix : r2 ∈ fixedIdxs pa.1 pa.2 := by
                    simp only [fixedIdxs, List.mem_filter, List.mem_range, decide_eq_true_eq]
                    exact ⟨hr2_lt, hr_idem idx2 hidx2_lt⟩
                  have he1_S : elem1 ∈ S :=
                    (mem_symLiveExts_iff E ctx pa.1 pa.2 elem1).mpr ⟨hr1_fix, hu1_blk, rfl, hl1⟩
                  have he2_S : elem2 ∈ S :=
                    (mem_symLiveExts_iff E ctx pa.1 pa.2 elem2).mpr ⟨hr2_fix, hu2_blk, rfl, hl2⟩
                  have hadj12 : symExtAdj I pa.1 elem1 elem2 = true := by
                    unfold symExtAdj extEqNat
                    simp only [orBool_eq, Bool.or_eq_true]
                    exact hadj_ext.elim (fun h => Or.inl (hext12.1 h)) (fun h => Or.inr (hext12.2 h))
                  have hadj21 : symExtAdj I pa.1 elem2 elem1 = true := by
                    unfold symExtAdj extEqNat
                    simp only [orBool_eq, Bool.or_eq_true]
                    exact hadj_ext.elim (fun h => Or.inl (hext21.1 h.symm)) (fun h => Or.inr (hext21.2 h.symm))
                  -- Show `elem1` and `elem2` appear in the EXACT SAME components `comps[d]`!
                  have hsame_comp : ∀ d < comps.length,
                      (cIdxOf (comps.getD d []) elem1 < (comps.getD d []).length) ↔
                      (cIdxOf (comps.getD d []) elem2 < (comps.getD d []).length) :=
                    symComponents_same_hit E ctx pa hfix_le elem1 elem2 he1_S he2_S hadj12 hadj21
                  have hhits_eq : hits1 = hits2 := by
                    unfold hits1 hits2 findHitComps
                    apply List.filter_congr
                    intro d hd
                    simp only [decide_eq_decide]
                    exact hsame_comp d (List.mem_range.mp hd)
                  rw [← hhits_eq] at h2_s
                  by_cases hlen_h : hits1.length = 0
                  · rw [if_pos hlen_h] at h1_s; cases h1_s
                  · rw [if_neg hlen_h] at h1_s h2_s
                    rcases Prod.mk.inj h1_s with ⟨_, h1p⟩
                    rcases Prod.mk.inj h1p with ⟨haddr1'_eq, hidx1'_eq⟩
                    rcases Prod.mk.inj h2_s with ⟨_, h2p⟩
                    rcases Prod.mk.inj h2p with ⟨haddr2'_eq, hidx2'_eq⟩
                    refine ⟨haddr1'_eq.symm.trans haddr2'_eq, ?_⟩
                    let d := hits1.getD 0 0
                    have hd_mem : d ∈ hits1 := by
                      dsimp only [d]; rw [getD_eq_getElem hits1 0 0 (by omega)]; exact List.getElem_mem _
                    have hd_mem' : d < comps.length ∧ cIdxOf (comps.getD d []) elem1 < (comps.getD d []).length := by
                      simpa only [hits1, findHitComps, List.mem_filter, List.mem_range, decide_eq_true_eq] using hd_mem
                    have hd_lt : d < comps.length := hd_mem'.1
                    let comp : List SymExtElem := comps[d]'hd_lt
                    have hcomp_get : comps.getD d [] = comp := getD_eq_getElem comps [] d hd_lt
                    have he1_in : elem1 ∈ comp := by
                      have := hd_mem'.2
                      rwa [cIdxOf_lt_iff_mem, hcomp_get] at this
                    have he2_in : elem2 ∈ comp := by
                      have := (hsame_comp d hd_lt).mp hd_mem'.2
                      rwa [cIdxOf_lt_iff_mem, hcomp_get] at this
                    have hcomps_le : comps.length ≤ B_full :=
                      (symComponents_props E ctx pa.1 pa.2 hfix_le).1
                    have hd_lt_ts : d < ts.1 + 1 := by
                      rw [hB_succ]; exact lt_of_lt_of_le hd_lt hcomps_le
                    let dFin : Fin (ts.1 + 1) := ⟨d, hd_lt_ts⟩
                    have hFin_d : dFin.val = d := by dsimp only [dFin]
                    have hch_ok := hchild_ok addrFin dFin
                    rw [tsChildOk_buildTreeSpec, ← hlabels_def, if_neg ha_ne,
                      getD_eq_getElem labels _ _ ha_lt, hFin_d] at hch_ok
                    dsimp only at hch_ok
                    rw [if_pos hd_lt] at hch_ok
                    by_cases ha'_zero : (tTree (addrFin ++ [dFin])).val = 0
                    · rw [if_pos ha'_zero] at hch_ok; cases hch_ok
                    · rw [if_neg ha'_zero, decide_eq_true_eq] at hch_ok
                      have hch_ok' : (labels.getD ((tTree (addrFin ++ [dFin])).val - 1)
                          (initSymPos, ([], [], []))).1 = childSymPos I pa.1 (comps.getD d []) := by
                        dsimp only [pa, comps, ctxI, ctx]; exact hch_ok
                      have ha'_eq : (E.unfoldLabelPacked tpσ addr1') % (labels.length + 1) =
                          (tTree (addrFin ++ [dFin])).val := by
                        dsimp only [tTree]
                        rw [← haddr1'_eq, haddr_fin, List.map_append, List.map_singleton, hFin_d, hts_len]
                      have hd_raw : hits1.getD 0 0 = d := by dsimp only [d]
                      have hidx1_c : idx1' = cIdxOf comp elem1 := by
                        rw [← hidx1'_eq, hd_raw, hcomp_get]
                      have hidx2_c : idx2' = cIdxOf comp elem2 := by
                        rw [← hidx2'_eq, hd_raw, hcomp_get]
                      dsimp only
                      rw [ha'_eq, hch_ok', hcomp_get, hidx1_c, hidx2_c]
                      have hacc := childSymPos_access I pa.1 comp
                      have hc_e1 := hacc.2.1
                      have hc_e2 := hacc.2.2.1
                      have hj1_sp := cIdxOf_lt_and_getElem he1_in
                      have hj2_sp := cIdxOf_lt_and_getElem he2_in
                      rw [hc_e1 _ hj1_sp.1 _ hj2_sp.1, hc_e2 _ hj1_sp.1 _ hj2_sp.1, hj1_sp.2, hj2_sp.2]
                      exact hext12
                · rw [if_neg hl2] at h2; cases h2
              · rw [if_neg hl1] at h1; cases h1

lemma evalViewPacked_of_valid_cand (E : Thm34Engine)
    (I : Instance) (D_m1 D : ℕ) (hD_def : D = D_m1 + 1)
    (bCode : GenDPACode) (liveList : List Bool)
    (ctx : SymCtx) (hctx_def : ctx = (I, D_m1, bCode, liveList))
    (ts : TreeSpecCode) (hts_def : ts = buildTreeSpec E ctx)
    (σ : List ℕ) (hsol : E.solveTreePG ts = some σ)
    (tpσ : ℕ) (htpσ_def : tpσ = Nat.pair (E.packTS ts) (Encodable.encode σ)) :
    ∀ (dep : ℕ), 1 ≤ dep →
      ∀ (wFull : List ℕ),
        wFull ∈ wordsOf (List.range (sigCard I)) dep →
        ∀ addr idx,
          traceBlocksNat E ctx tpσ (sliceNat wFull 0 (((dep - 1) / D) * D)) = (true, addr, idx) →
          evalViewPacked E ctx (Nat.pair tpσ (Nat.pair 0 (Encodable.encode (view1 (decHist I wFull))))) =
            evalCandOutNat E ctx tpσ 0 addr idx
              (sliceNat wFull (((dep - 1) / D) * D) (dep - ((dep - 1) / D) * D)) ∧
          evalViewPacked E ctx (Nat.pair tpσ (Nat.pair 1 (Encodable.encode (view2 (decHist I wFull))))) =
            evalCandOutNat E ctx tpσ 1 addr idx
              (sliceNat wFull (((dep - 1) / D) * D) (dep - ((dep - 1) / D) * D)) := by
  subst hD_def
  subst hctx_def
  subst hts_def
  subst htpσ_def
  let D := D_m1 + 1
  have hD_pos : 0 < D := Nat.succ_pos D_m1
  let ctx : SymCtx := (I, D_m1, bCode, liveList)
  let ts := buildTreeSpec E ctx
  let tpσ := Nat.pair (E.packTS ts) (Encodable.encode σ)
  obtain ⟨labels, hlabels_def⟩ : ∃ l, l = validSymLabels ctx := ⟨_, rfl⟩
  have hts_len : ts.2.1 = labels.length := by rw [hlabels_def]; rfl
  let tTree : List (Fin (ts.1 + 1)) → Fin (ts.2.1 + 1) := fun addr =>
    ⟨(E.unfoldLabelPacked tpσ (addr.map Fin.val)) % (ts.2.1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  have htraceBlocks_eq_fold := fun m wPre (hlen : wPre.length = m * D) =>
    traceBlocksNat_eq_foldBlocksNat E I D_m1 D rfl bCode liveList ctx rfl tpσ m wPre hlen
  have hfold_valid := foldBlocksNat_valid E I D_m1 D rfl bCode liveList ctx rfl ts rfl σ hsol tpσ rfl
    tTree rfl labels hlabels_def
  have hfold_hom := foldBlocksNat_hom E I D_m1 D rfl bCode liveList ctx rfl ts rfl σ hsol tpσ rfl
    labels hlabels_def
  -- Uniqueness of `evalCandOutNat` across all valid candidates matching `vCode`
  have hevalCand_unique : ∀ (dep : ℕ), 1 ≤ dep →
      let n := (dep - 1) / D
      ∀ (w1 w2 : List ℕ),
        w1 ∈ wordsOf (List.range (sigCard I)) dep →
        w2 ∈ wordsOf (List.range (sigCard I)) dep →
        ∀ addr1 idx1 addr2 idx2,
          traceBlocksNat E ctx tpσ (sliceNat w1 0 (n * D)) = (true, addr1, idx1) →
          traceBlocksNat E ctx tpσ (sliceNat w2 0 (n * D)) = (true, addr2, idx2) →
          (((viewsNatOfCode I w1).1 = (viewsNatOfCode I w2).1 →
            evalCandOutNat E ctx tpσ 0 addr1 idx1 (sliceNat w1 (n * D) (dep - n * D)) =
              evalCandOutNat E ctx tpσ 0 addr2 idx2 (sliceNat w2 (n * D) (dep - n * D))) ∧
           ((viewsNatOfCode I w1).2 = (viewsNatOfCode I w2).2 →
            evalCandOutNat E ctx tpσ 1 addr1 idx1 (sliceNat w1 (n * D) (dep - n * D)) =
              evalCandOutNat E ctx tpσ 1 addr2 idx2 (sliceNat w2 (n * D) (dep - n * D)))) := by
    intro dep hdep n w1 w2 hw1 hw2 addr1 idx1 addr2 idx2 htr1 htr2
    obtain ⟨hw1_len, hw1_lt⟩ := (mem_wordsOf_iff _ dep w1).mp hw1
    obtain ⟨hw2_len, hw2_lt⟩ := (mem_wordsOf_iff _ dep w2).mp hw2
    simp only [List.mem_range] at hw1_lt hw2_lt
    have hnD_lt : n * D < dep := by
      have hdiv_mod := Nat.div_add_mod (dep - 1) D
      have hmul_comm : D * ((dep - 1) / D) = n * D := Nat.mul_comm D n
      omega
    have hnD_le : n * D ≤ dep := Nat.le_of_lt hnD_lt
    have hrem_le : dep - n * D ≤ D := by
      have hdiv_mod := Nat.div_add_mod (dep - 1) D
      have hmod_lt : (dep - 1) % D < D := Nat.mod_lt (dep - 1) hD_pos
      have hmul_comm : D * ((dep - 1) / D) = n * D := Nat.mul_comm D n
      omega
    have hsl_pre1 : sliceNat w1 0 (n * D) = w1.take (n * D) := by
      simpa using sliceNat_eq_take_drop w1 0 (n * D) (by omega)
    have hsl_pre2 : sliceNat w2 0 (n * D) = w2.take (n * D) := by
      simpa using sliceNat_eq_take_drop w2 0 (n * D) (by omega)
    have hsl_suf1 : sliceNat w1 (n * D) (dep - n * D) = w1.drop (n * D) := by
      rw [sliceNat_eq_take_drop w1 (n * D) (dep - n * D) (by omega)]
      exact List.take_of_length_le (by simp [hw1_len])
    have hsl_suf2 : sliceNat w2 (n * D) (dep - n * D) = w2.drop (n * D) := by
      rw [sliceNat_eq_take_drop w2 (n * D) (dep - n * D) (by omega)]
      exact List.take_of_length_le (by simp [hw2_len])
    rw [hsl_pre1] at htr1
    rw [hsl_pre2] at htr2
    rw [hsl_suf1, hsl_suf2]
    let us1 := (List.range n).map fun k => ((w1.take (n * D)).drop (k * D)).take D
    let us2 := (List.range n).map fun k => ((w2.take (n * D)).drop (k * D)).take D
    have hlen_pre1 : (w1.take (n * D)).length = n * D := by simp [hw1_len, hnD_le]
    have hlen_pre2 : (w2.take (n * D)).length = n * D := by simp [hw2_len, hnD_le]
    rw [htraceBlocks_eq_fold n _ hlen_pre1] at htr1
    rw [htraceBlocks_eq_fold n _ hlen_pre2] at htr2
    have hus_flatten : ∀ (w : List ℕ) (hw_l : w.length = dep) (hw_b : ∀ x ∈ w, x < sigCard I),
        let us := (List.range n).map fun k => ((w.take (n * D)).drop (k * D)).take D
        (∀ u ∈ us, u ∈ fullBlocks I D) ∧ us.flatten = w.take (n * D) := by
      intro w hw_l hw_b us
      have hlen_t : (w.take (n * D)).length = n * D := by simp [hw_l, hnD_le]
      refine ⟨?_, ?_⟩
      · intro u hu
        simp only [us, List.mem_map, List.mem_range] at hu
        rcases hu with ⟨k, hk, rfl⟩
        rw [mem_fullBlocks_iff]
        have hk1 : k * D + D ≤ n * D := by
          simpa [Nat.succ_mul] using Nat.mul_le_mul_right D hk
        have htake_len : (((w.take (n * D)).drop (k * D)).take D).length = D := by
          rw [List.length_take, List.length_drop, hlen_t]
          omega
        refine ⟨htake_len, ?_⟩
        intro x hx
        exact hw_b x (List.mem_of_mem_take (List.mem_of_mem_drop (List.mem_of_mem_take hx)))
      · have hcat : ∀ m ≤ n,
            ((List.range m).map fun k => ((w.take (n * D)).drop (k * D)).take D).flatten =
              (w.take (n * D)).take (m * D) := by
          intro m hm
          induction m with
          | zero => simp
          | succ m ihm =>
            rw [List.range_succ, List.map_append, List.map_singleton, List.flatten_append,
              List.flatten_singleton, ihm (by omega)]
            have hm_le : m * D ≤ n * D := Nat.mul_le_mul_right D (Nat.le_of_succ_le hm)
            have hm1_le : m * D + D ≤ n * D := by
              simpa [Nat.succ_mul] using Nat.mul_le_mul_right D hm
            have hlen_l : ((w.take (n * D)).take (m * D)).length = m * D := by
              rw [List.length_take, hlen_t, min_eq_left hm_le]
            have hlen_r : (((w.take (n * D)).drop (m * D)).take D).length = D := by
              rw [List.length_take, List.length_drop, hlen_t]
              omega
            have hlen_rhs : ((w.take (n * D)).take ((m + 1) * D)).length = m * D + D := by
              rw [Nat.succ_mul, List.length_take, hlen_t, min_eq_left hm1_le]
            apply List.ext_getElem
            · rw [List.length_append, hlen_l, hlen_r, hlen_rhs]
            · intro idx hi1 hi2
              rw [hlen_rhs] at hi2
              by_cases hlt_m : idx < m * D
              · rw [List.getElem_append_left (by rw [hlen_l]; exact hlt_m)]
                simp only [List.getElem_take]
              · rw [List.getElem_append_right (by rw [hlen_l]; omega)]
                simp only [hlen_l, List.getElem_take, List.getElem_drop]
                congr 1; omega
        simpa [List.take_take, min_self] using hcat n (le_refl n)
    obtain ⟨hus1_blk, hus1_fl⟩ := hus_flatten w1 hw1_len hw1_lt
    obtain ⟨hus2_blk, hus2_fl⟩ := hus_flatten w2 hw2_len hw2_lt
    have hus_len : us1.length = us2.length := by simp [us1, us2]
    have hw1_split : decHist I w1 = decHist I (w1.take (n * D)) ++ decHist I (w1.drop (n * D)) := by
      unfold decHist; rw [← List.map_append, List.take_append_drop]
    have hw2_split : decHist I w2 = decHist I (w2.take (n * D)) ++ decHist I (w2.drop (n * D)) := by
      unfold decHist; rw [← List.map_append, List.take_append_drop]
    have hwsuf1_in : w1.drop (n * D) ∈ nonemptyExtWords I D := by
      rw [mem_nonemptyExtWords_iff]
      exact ⟨by simp [hw1_len]; omega, by simp [hw1_len]; omega,
        fun x hx => hw1_lt x (List.mem_of_mem_drop hx)⟩
    have hwsuf2_in : w2.drop (n * D) ∈ nonemptyExtWords I D := by
      rw [mem_nonemptyExtWords_iff]
      exact ⟨by simp [hw2_len]; omega, by simp [hw2_len]; omega,
        fun x hx => hw2_lt x (List.mem_of_mem_drop hx)⟩
    obtain ⟨hwi1_lt, hwi1_get⟩ := cIdxOf_lt_and_getElem hwsuf1_in
    obtain ⟨hwi2_lt, hwi2_get⟩ := cIdxOf_lt_and_getElem hwsuf2_in
    have hprove_proc : ∀ (p : Proc),
        viewOf p (decHist I w1) = viewOf p (decHist I w2) →
        evalCandOutNat E ctx tpσ (if p = .one then 0 else 1) addr1 idx1 (w1.drop (n * D)) =
          evalCandOutNat E ctx tpσ (if p = .one then 0 else 1) addr2 idx2 (w2.drop (n * D)) := by
      intro p hv_full
      rw [hw1_split, hw2_split] at hv_full
      have hlen_dh : (decHist I (w1.take (n * D))).length = (decHist I (w2.take (n * D))).length := by
        rw [decHist, decHist, List.length_map, List.length_map, hlen_pre1, hlen_pre2]
      have hv_pre : viewOf p (decHist I (w1.take (n * D))) = viewOf p (decHist I (w2.take (n * D))) :=
        (viewOf_prefix_eq hlen_dh hv_full).2
      have hadj_pre : EdgeAdj (decHist I us1.flatten) (decHist I us2.flatten) := by
        rw [hus1_fl, hus2_fl]
        cases p with
        | one => exact Or.inl hv_pre
        | two => exact Or.inr hv_pre
      obtain ⟨haddr_eq, hhom⟩ := hfold_hom us1 us2 hus_len hus1_blk hus2_blk
        addr1 idx1 addr2 idx2 htr1 htr2 hadj_pre
      subst haddr_eq
      rw [hus1_fl, hus2_fl] at hhom
      obtain ⟨addrFin, haddr_fin, _, _, ha_lt, hpa_mem, hidx1_lt⟩ :=
        hfold_valid us1 hus1_blk addr1 idx1 htr1
      obtain ⟨addrFin2, haddr_fin2, _, _, _, _, hidx2_lt⟩ :=
        hfold_valid us2 hus2_blk addr1 idx2 htr2
      have hw_eq : addrFin2 = addrFin :=
        List.map_injective_iff.mpr Fin.val_injective (haddr_fin2.symm.trans haddr_fin)
      rw [hw_eq] at hidx2_lt
      dsimp only at hhom
      rw [getD_eq_getElem labels _ _ ha_lt] at hpa_mem hidx1_lt hidx2_lt
      have ha_eq : (E.unfoldLabelPacked tpσ addr1) % (labels.length + 1) = (tTree addrFin).val := by
        dsimp only [tTree]; rw [haddr_fin, hts_len]
      let pa := labels[(tTree addrFin).val - 1]'ha_lt
      have hpa_get : labels.getD ((E.unfoldLabelPacked tpσ addr1) % (labels.length + 1) - 1)
          (initSymPos, ([], [], [])) = pa := by
        rw [ha_eq, getD_eq_getElem labels _ _ ha_lt]
      rw [hpa_get] at hhom
      have hpa_mem' : pa ∈ validSymLabels ctx := hlabels_def ▸ hpa_mem
      have hact_valid := ((mem_validSymLabels_iff ctx pa).mp hpa_mem').2.2
      unfold actValid at hact_valid
      rw [decide_eq_true_eq] at hact_valid
      obtain ⟨hr_idem, _, _, hr_vw, hout_coh⟩ := hact_valid
      have hact_mem := ((mem_validSymLabels_iff ctx pa).mp hpa_mem').2.1
      rw [mem_allSymActsFor_iff] at hact_mem
      let r1 := pa.2.1.getD idx1 0
      let r2 := pa.2.1.getD idx2 0
      have hr1_lt : r1 < pa.1.1 := by
        dsimp [r1]; rw [getD_eq_getElem pa.2.1 0 idx1 (hact_mem.1 ▸ hidx1_lt)]
        exact hact_mem.2.1 _ (List.getElem_mem _)
      have hr2_lt : r2 < pa.1.1 := by
        dsimp [r2]; rw [getD_eq_getElem pa.2.1 0 idx2 (hact_mem.1 ▸ hidx2_lt)]
        exact hact_mem.2.1 _ (List.getElem_mem _)
      have hr1_fix : r1 ∈ fixedIdxs pa.1 pa.2 := by
        simp only [fixedIdxs, List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨hr1_lt, hr_idem idx1 hidx1_lt⟩
      have hr2_fix : r2 ∈ fixedIdxs pa.1 pa.2 := by
        simp only [fixedIdxs, List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨hr2_lt, hr_idem idx2 hidx2_lt⟩
      have hr_hom1 : view1 (decHist I (w1.take (n * D))) = view1 (decHist I (w2.take (n * D))) →
          eq1At pa.1 r1 r2 = true := by
        dsimp only [r1, r2]; exact fun hv => (hr_vw idx1 hidx1_lt idx2 hidx2_lt).1 (hhom.1 hv)
      have hr_hom2 : view2 (decHist I (w1.take (n * D))) = view2 (decHist I (w2.take (n * D))) →
          eq2At pa.1 r1 r2 = true := by
        dsimp only [r1, r2]; exact fun hv => (hr_vw idx1 hidx1_lt idx2 hidx2_lt).2 (hhom.2 hv)
      have hext := extEqFrom_of_hom I hlen_dh hr_hom1 hr_hom2 (w1.drop (n * D)) (w2.drop (n * D))
      let words := nonemptyExtWords I D
      let wi1 := cIdxOf words (w1.drop (n * D))
      let wi2 := cIdxOf words (w2.drop (n * D))
      have hw1_get : words.getD wi1 [] = w1.drop (n * D) := by
        rw [getD_eq_getElem words [] wi1 hwi1_lt]; exact hwi1_get
      have hw2_get : words.getD wi2 [] = w2.drop (n * D) := by
        rw [getD_eq_getElem words [] wi2 hwi2_lt]; exact hwi2_get
      have hcoh := hout_coh r1 hr1_fix r2 hr2_fix wi1 hwi1_lt wi2 hwi2_lt
      dsimp only [ctxI, ctxD, ctx] at hcoh
      rw [hw1_get, hw2_get] at hcoh
      unfold evalCandOutNat
      rw [← hlabels_def]
      dsimp only [ctxI, ctxD, ctx]
      rw [hpa_get]
      cases p with
      | one =>
        simp only [↓reduceIte]
        rw [hcoh.1 (hext.1 hv_full)]
      | two =>
        simp only [reduceCtorEq, ↓reduceIte, one_ne_zero]
        rw [hcoh.2 (hext.2 hv_full)]
    rw [viewsNatOfCode_eq_encode I w1, viewsNatOfCode_eq_encode I w2]
    exact ⟨fun hv1 => hprove_proc .one (Encodable.encode_injective hv1),
      fun hv2 => hprove_proc .two (Encodable.encode_injective hv2)⟩
  -- Corollary: `evalViewPacked` on any valid candidate returns its `evalCandOutNat`
  have hevalView_of_cand : ∀ (dep : ℕ), 1 ≤ dep →
      let n := (dep - 1) / D
      ∀ (wFull : List ℕ),
        wFull ∈ wordsOf (List.range (sigCard I)) dep →
        ∀ addr idx,
          traceBlocksNat E ctx tpσ (sliceNat wFull 0 (n * D)) = (true, addr, idx) →
          evalViewPacked E ctx (Nat.pair tpσ (Nat.pair 0 (Encodable.encode (view1 (decHist I wFull))))) =
            evalCandOutNat E ctx tpσ 0 addr idx (sliceNat wFull (n * D) (dep - n * D)) ∧
          evalViewPacked E ctx (Nat.pair tpσ (Nat.pair 1 (Encodable.encode (view2 (decHist I wFull))))) =
            evalCandOutNat E ctx tpσ 1 addr idx (sliceNat wFull (n * D) (dep - n * D)) := by
    intro dep hdep n wFull hwFull addr idx htr
    have hw_len : wFull.length = dep := ((mem_wordsOf_iff _ dep wFull).mp hwFull).1
    have hd1 : vdepthNat (Encodable.encode (view1 (decHist I wFull))) = dep := by
      rw [vdepthNat_encode, (vdepth_views _).1, decHist, List.length_map, hw_len]
    have hd2 : vdepthNat (Encodable.encode (view2 (decHist I wFull))) = dep := by
      rw [vdepthNat_encode, (vdepth_views _).2, decHist, List.length_map, hw_len]
    have hd_ne : dep ≠ 0 := by omega
    have hctxI : ctxI ctx = I := rfl
    have hctxD : ctxD ctx = D := rfl
    unfold evalViewPacked
    simp only [Nat.unpair_pair, hd1, hd2, if_neg hd_ne, ↓reduceIte, one_ne_zero, hctxI, hctxD]
    constructor
    · let hits := (wordsOf (List.range (sigCard I)) dep).flatMap fun w =>
        let vPair := viewsNatOfCode I w
        if decide (vPair.1 = Encodable.encode (view1 (decHist I wFull))) = true then
          let tr := traceBlocksNat E ctx tpσ (sliceNat w 0 (n * D))
          if tr.1 = true then
            [evalCandOutNat E ctx tpσ 0 tr.2.1 tr.2.2 (sliceNat w (n * D) (dep - n * D))]
          else []
        else []
      let target := evalCandOutNat E ctx tpσ 0 addr idx (sliceNat wFull (n * D) (dep - n * D))
      have hmem_target : target ∈ hits := by
        simp only [hits, List.mem_flatMap]
        refine ⟨wFull, hwFull, ?_⟩
        rw [viewsNatOfCode_eq_encode I wFull]
        simp [htr, target]
      have hall_eq : ∀ y ∈ hits, y = target := by
        intro y hy
        simp only [hits, List.mem_flatMap] at hy
        rcases hy with ⟨w, hw, hmy⟩
        by_cases hvm : decide ((viewsNatOfCode I w).1 = Encodable.encode (view1 (decHist I wFull))) = true
        · rw [if_pos hvm] at hmy
          let tr := traceBlocksNat E ctx tpσ (sliceNat w 0 (n * D))
          change y ∈ (if tr.1 = true then
            [evalCandOutNat E ctx tpσ 0 tr.2.1 tr.2.2 (sliceNat w (n * D) (dep - n * D))]
          else []) at hmy
          by_cases htrok : tr.1 = true
          · rw [if_pos htrok] at hmy
            simp only [List.mem_singleton] at hmy
            rw [hmy]
            have hveq : (viewsNatOfCode I w).1 = (viewsNatOfCode I wFull).1 := by
              rw [viewsNatOfCode_eq_encode I wFull]; exact of_decide_eq_true hvm
            exact (hevalCand_unique dep hdep w wFull hw hwFull tr.2.1 tr.2.2 addr idx
              (Prod.ext htrok rfl) htr).1 hveq
          · rw [if_neg htrok] at hmy; cases hmy
        · rw [if_neg hvm] at hmy; cases hmy
      have hpos_h : 0 < hits.length := List.length_pos_of_mem hmem_target
      change hits.getD 0 0 = target
      rw [getD_eq_getElem hits 0 0 hpos_h]
      exact hall_eq _ (List.getElem_mem hpos_h)
    · let hits := (wordsOf (List.range (sigCard I)) dep).flatMap fun w =>
        let vPair := viewsNatOfCode I w
        if decide (vPair.2 = Encodable.encode (view2 (decHist I wFull))) = true then
          let tr := traceBlocksNat E ctx tpσ (sliceNat w 0 (n * D))
          if tr.1 = true then
            [evalCandOutNat E ctx tpσ 1 tr.2.1 tr.2.2 (sliceNat w (n * D) (dep - n * D))]
          else []
        else []
      let target := evalCandOutNat E ctx tpσ 1 addr idx (sliceNat wFull (n * D) (dep - n * D))
      have hmem_target : target ∈ hits := by
        simp only [hits, List.mem_flatMap]
        refine ⟨wFull, hwFull, ?_⟩
        rw [viewsNatOfCode_eq_encode I wFull]
        simp [htr, target]
      have hall_eq : ∀ y ∈ hits, y = target := by
        intro y hy
        simp only [hits, List.mem_flatMap] at hy
        rcases hy with ⟨w, hw, hmy⟩
        by_cases hvm : decide ((viewsNatOfCode I w).2 = Encodable.encode (view2 (decHist I wFull))) = true
        · rw [if_pos hvm] at hmy
          let tr := traceBlocksNat E ctx tpσ (sliceNat w 0 (n * D))
          change y ∈ (if tr.1 = true then
            [evalCandOutNat E ctx tpσ 1 tr.2.1 tr.2.2 (sliceNat w (n * D) (dep - n * D))]
          else []) at hmy
          by_cases htrok : tr.1 = true
          · rw [if_pos htrok] at hmy
            simp only [List.mem_singleton] at hmy
            rw [hmy]
            have hveq : (viewsNatOfCode I w).2 = (viewsNatOfCode I wFull).2 := by
              rw [viewsNatOfCode_eq_encode I wFull]; exact of_decide_eq_true hvm
            exact (hevalCand_unique dep hdep w wFull hw hwFull tr.2.1 tr.2.2 addr idx
              (Prod.ext htrok rfl) htr).2 hveq
          · rw [if_neg htrok] at hmy; cases hmy
        · rw [if_neg hvm] at hmy; cases hmy
      have hpos_h : 0 < hits.length := List.length_pos_of_mem hmem_target
      change hits.getD 0 0 = target
      rw [getD_eq_getElem hits 0 0 hpos_h]
      exact hall_eq _ (List.getElem_mem hpos_h)
  exact hevalView_of_cand

/-- Soundness of the symbolic compressed tree game and executable readback:
if `E.solveTreePG (buildTreeSpec E ctx) = some σ`, then the local algorithm computed by
`evalViewPacked` realizes `instFormulaOf I φ` under `c.lang`. -/
lemma soundness_of_solveTreePG_some (E : Thm34Engine)
    (c : DPACode) (I : Instance) (D_m1 : ℕ) (φ : Formula ℕ ℕ ℕ ℕ)
    (hparse : parse I.tokens = some φ)
    (σ : List ℕ)
    (hsol : E.solveTreePG (buildTreeSpec E (I, D_m1, (E.compileBlock (c, I, D_m1)).1,
      (E.compileBlock (c, I, D_m1)).2)) = some σ) :
    let res := E.compileBlock (c, I, D_m1)
    let ctx : SymCtx := (I, D_m1, res.1, res.2)
    let ts := buildTreeSpec E ctx
    let tpσ := Nat.pair (E.packTS ts) (Encodable.encode σ)
    let f : Algorithm I.X1 I.X2 I.Y1 I.Y2 :=
      { f1 := fun v => ⟨evalViewPacked E ctx (Nat.pair tpσ (Nat.pair 0 (Encodable.encode v))),
          (evalViewPacked_lt E ctx tpσ (Encodable.encode v)).1⟩
        f2 := fun v => ⟨evalViewPacked E ctx (Nat.pair tpσ (Nat.pair 1 (Encodable.encode v))),
          (evalViewPacked_lt E ctx tpσ (Encodable.encode v)).2⟩ }
    FRealizes f c.lang (instFormulaOf I φ) := by
  dsimp only
  let D := D_m1 + 1
  have hD_pos : 0 < D := Nat.succ_pos D_m1
  let res := E.compileBlock (c, I, D_m1)
  let ctx : SymCtx := (I, D_m1, res.1, res.2)
  let ts := buildTreeSpec E ctx
  let tpσ := Nat.pair (E.packTS ts) (Encodable.encode σ)
  obtain ⟨labels, hlabels_def⟩ : ∃ l, l = validSymLabels ctx := ⟨_, rfl⟩
  have hts_len : ts.2.1 = labels.length := by rw [hlabels_def]; rfl
  let B_full := ctxBFull ctx
  have hB_succ : ts.1 + 1 = B_full := Nat.sub_add_cancel (ctxBFull_pos ctx)
  let dpa := toGenDPA (E.blockAlphaMinusOne I D) res.1
  let B : DPA (Fin (res.1.1 + 1)) (Fin D → Signal I.X1 I.X2 × (I.Y1 × I.Y2)) :=
    ⟨dpa.init, fun q blk => dpa.step q (E.encIOBlockTyped I D blk), dpa.prio⟩
  let Qlive : Set (Fin (res.1.1 + 1)) := {q | res.2.getD q.val false = true}
  have hB : IsBlockAutomaton c.lang (instFormulaOf I φ) D B Qlive :=
    E.compileBlock_spec c I D_m1 φ hparse
  let tTree : List (Fin (ts.1 + 1)) → Fin (ts.2.1 + 1) := fun addr =>
    ⟨(E.unfoldLabelPacked tpσ (addr.map Fin.val)) % (ts.2.1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  have hvat : ValidAcceptingTree ts tTree := E.solveTreePG_some_sound ts σ hsol
  obtain ⟨hroot_ok, hchild_ok, hbranch_acc⟩ := hvat
  have htraceBlocks_eq_fold := fun m wPre (hlen : wPre.length = m * D) =>
    traceBlocksNat_eq_foldBlocksNat E I D_m1 D rfl res.1 res.2 ctx rfl tpσ m wPre hlen
  have hfold_valid := foldBlocksNat_valid E I D_m1 D rfl res.1 res.2 ctx rfl ts rfl σ hsol tpσ rfl
    tTree rfl labels hlabels_def
  have hevalView_of_cand := evalViewPacked_of_valid_cand E I D_m1 D rfl res.1 res.2 ctx rfl ts rfl
    σ hsol tpσ rfl
  have hctxI : ctxI ctx = I := rfl
  have hctxD : ctxD ctx = D := rfl
  have hctxB : ctxBCode ctx = res.1 := rfl
  -- Now prove `FRealizes f c.lang (instFormulaOf I φ)` along any execution `e = exec f h_inf`!
  let f : Algorithm I.X1 I.X2 I.Y1 I.Y2 :=
    { f1 := fun v => ⟨evalViewPacked E ctx (Nat.pair tpσ (Nat.pair 0 (Encodable.encode v))),
        (evalViewPacked_lt E ctx tpσ (Encodable.encode v)).1⟩
      f2 := fun v => ⟨evalViewPacked E ctx (Nat.pair tpσ (Nat.pair 1 (Encodable.encode v))),
        (evalViewPacked_lt E ctx tpσ (Encodable.encode v)).2⟩ }
  change FRealizes f c.lang (instFormulaOf I φ)
  intro h_inf hg_in_A
  let e := exec f h_inf
  have hge_eq : graphOfExec e = graphOf h_inf := rfl
  have hlive_all : ∀ m : ℕ, B.run (toBlocks D e) m ∈ Qlive := by
    intro m
    rw [hB.live e m, hge_eq]
    exact ⟨graphOf h_inf, hg_in_A, by simp [pre]⟩
  -- Trace `uSeq m := encBlock I (toBlocks D h_inf m)` through `foldBlocksNat`
  let uSeq : ℕ → List ℕ := fun m => encBlock I (toBlocks D h_inf m)
  have huSeq_blk : ∀ m, uSeq m ∈ fullBlocks I D :=
    fun m => encBlock_mem_fullBlocks I (toBlocks D h_inf m)
  have hpre_blocks : ∀ m,
      traceBlocksNat E ctx tpσ (encHist I (pre h_inf (m * D))) =
        foldBlocksNat E ctx tpσ ((List.range m).map uSeq) := by
    intro m
    have hlen_m : (encHist I (pre h_inf (m * D))).length = m * D := by simp [encHist, pre]
    rw [htraceBlocks_eq_fold m _ hlen_m]
    congr 1
    apply List.map_congr_left
    intro k hk
    have hk_lt : k < m := List.mem_range.mp hk
    apply List.ext_getElem
    · have hk1 : k * D + D ≤ m * D := by
        simpa [Nat.succ_mul] using Nat.mul_le_mul_right D hk_lt
      rw [List.length_take, List.length_drop, hlen_m]
      simp only [uSeq, encBlock, encHist, List.length_map, List.length_ofFn]
      omega
    · intro j hj1 hj2
      have hj_lt : j < D := by
        simp only [uSeq, encBlock, encHist, List.length_map, List.length_ofFn] at hj2
        exact hj2
      simp only [List.getElem_take, List.getElem_drop, encHist, pre, List.getElem_map,
        List.getElem_ofFn, uSeq, encBlock, toBlocks]
  -- Inductive tracking of `foldBlocksNat E ctx tpσ ((List.range m).map uSeq)` and `B.run (toBlocks D e) m`
  have htrack : ∀ m : ℕ,
      ∃ (addrFin : List (Fin (ts.1 + 1))) (idx : ℕ),
        foldBlocksNat E ctx tpσ ((List.range m).map uSeq) = (true, addrFin.map Fin.val, idx) ∧
        addrFin.length = m ∧
        idx < B_full ∧
        let a := (tTree addrFin).val
        let pa := labels.getD (a - 1) (initSymPos, ([], [], []))
        stateAt pa.1 idx = (B.run (toBlocks D e) m).val ∧
        (∀ m0, m = m0 + 1 →
          ∃ (addrPrev : List (Fin (ts.1 + 1))) (dFin : Fin (ts.1 + 1)) (idxPrev : ℕ),
            addrFin = addrPrev ++ [dFin] ∧
            foldBlocksNat E ctx tpσ ((List.range m0).map uSeq) = (true, addrPrev.map Fin.val, idxPrev) ∧
            edgeStepOk E ctx labels (tTree addrPrev).val dFin.val idxPrev
              (B.prio (B.run (toBlocks D e) m)) idx = true) := by
    intro m
    induction m with
    | zero =>
      refine ⟨[], 0, rfl, rfl, ctxBFull_pos ctx, ?_, fun _ hm => by omega⟩
      rw [tsRootOk_buildTreeSpec, ← hlabels_def] at hroot_ok
      by_cases ha0 : (tTree []).val = 0
      · rw [if_pos ha0] at hroot_ok; cases hroot_ok
      · rw [if_neg ha0, decide_eq_true_eq] at hroot_ok
        rw [hroot_ok]
        rfl
    | succ m ih =>
      obtain ⟨addrFin, idx, hfold_m, hlen_m, _, hst_m, _⟩ := ih
      have hus_m_blk : ∀ u ∈ (List.range m).map uSeq, u ∈ fullBlocks I D := by
        intro u hu; obtain ⟨k, _, rfl⟩ := List.mem_map.mp hu; exact huSeq_blk k
      obtain ⟨addrFin', hmap_eq', _, ha_ne, ha_lt, hpa_mem, hidx_lt⟩ :=
        hfold_valid ((List.range m).map uSeq) hus_m_blk (addrFin.map Fin.val) idx hfold_m
      have hfin_eq : addrFin' = addrFin :=
        List.map_injective_iff.mpr Fin.val_injective hmap_eq'.symm
      rw [hfin_eq] at ha_ne ha_lt hpa_mem hidx_lt
      rw [getD_eq_getElem labels _ _ ha_lt] at hpa_mem hidx_lt
      let pa := labels[(tTree addrFin).val - 1]'ha_lt
      have hpa_get : labels.getD ((tTree addrFin).val - 1) (initSymPos, ([], [], [])) = pa :=
        getD_eq_getElem labels _ _ ha_lt
      rw [hpa_get] at hst_m
      have hpa_mem' : pa ∈ validSymLabels ctx := hlabels_def ▸ hpa_mem
      have hact_valid := ((mem_validSymLabels_iff ctx pa).mp hpa_mem').2.2
      unfold actValid at hact_valid
      rw [decide_eq_true_eq] at hact_valid
      obtain ⟨hr_idem, hfix_le, hr_st, _, _⟩ := hact_valid
      have hact_mem := ((mem_validSymLabels_iff ctx pa).mp hpa_mem').2.1
      rw [mem_allSymActsFor_iff] at hact_mem
      let r := pa.2.1.getD idx 0
      have hr_lt : r < pa.1.1 := by
        dsimp [r]; rw [getD_eq_getElem pa.2.1 0 idx (hact_mem.1 ▸ hidx_lt)]
        exact hact_mem.2.1 _ (List.getElem_mem _)
      -- Show `symNextState E ctx pa.1 pa.2 r (uSeq m) = (B.run (toBlocks D e) (m + 1)).val`
      let words := nonemptyExtWords I D
      let NW := words.length
      have hq'_eq : symNextState E ctx pa.1 pa.2 r (uSeq m) =
          (B.run (toBlocks D e) (m + 1)).val := by
        change symNextState E ctx pa.1 pa.2 r (uSeq m) =
          (B.step (B.run (toBlocks D e) m) (toBlocks D e m)).val
        unfold symNextState
        rw [hctxI, hctxD, hctxB]
        have hB_step : ∀ (q : Fin (res.1.1 + 1)) (blk : Fin D → Signal I.X1 I.X2 × (I.Y1 × I.Y2)),
            (B.step q blk).val =
              (res.1.2.1.getD (q.val * (E.blockAlphaMinusOne I D + 1) +
                (E.encIOBlockTyped I D blk).val) 0) % (res.1.1 + 1) := fun _ _ => rfl
        have hst_r : stateAt pa.1 r = (B.run (toBlocks D e) m).val :=
          (hr_st idx hidx_lt).trans hst_m
        rw [hst_r, hB_step, E.encIOBlock_compat I D (toBlocks D e m)]
        dsimp only
        have hio_eq : ((List.range D).map fun t =>
            let s := (uSeq m).getD t 0
            let wi := cIdxOf words ((uSeq m).take (t + 1))
            (decSigX1 I s, decSigX2 I s, decSigG s,
              pa.2.2.1.getD (r * NW + wi) 0,
              pa.2.2.2.getD (r * NW + wi) 0)) =
            ((List.ofFn (toBlocks D e m)).map fun s =>
              (s.1.1.val, s.1.2.1.val, s.1.2.2.idx, s.2.1.val, s.2.2.val)) := by
          apply List.ext_getElem
          · rw [List.length_map, List.length_range, List.length_map, List.length_ofFn]
          · intro t ht1 ht2
            have ht_lt : t < D := by rw [List.length_map, List.length_range] at ht1; exact ht1
            let tf : Fin D := ⟨t, ht_lt⟩
            simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
            have hs_eq : (uSeq m).getD t 0 = encSigTyped I (h_inf (m * D + t)) := by
              have hlen_um : (uSeq m).length = D := by
                simp only [uSeq, encBlock, encHist, List.length_map, List.length_ofFn]
              rw [getD_eq_getElem _ 0 t (by omega)]
              simp only [uSeq, encBlock, encHist, toBlocks, List.getElem_map, List.getElem_ofFn]
            obtain ⟨hx1, hx2, hg, _⟩ := decSigFields_encSigTyped I (h_inf (m * D + t))
            -- Match outputs at round `dep := m * D + t + 1` via `hevalView_of_cand`
            let dep := m * D + t + 1
            have hdep1 : 1 ≤ dep := Nat.succ_pos _
            have hdiv_dep : (dep - 1) / D = m := by
              have hrew : dep - 1 = t + D * m := by dsimp [dep]; ring
              rw [hrew, Nat.add_mul_div_left _ _ hD_pos, Nat.div_eq_of_lt ht_lt, zero_add]
            let wFull := encHist I (pre h_inf dep)
            have hwFull_in : wFull ∈ wordsOf (List.range (sigCard I)) dep := by
              rw [mem_wordsOf_iff]
              refine ⟨by simp only [wFull, encHist, pre, List.length_map, List.length_ofFn], ?_⟩
              intro x hx
              simp only [wFull, encHist, List.mem_map] at hx
              rcases hx with ⟨s0, _, rfl⟩
              exact List.mem_range.mpr (encSigTyped_lt I s0)
            have hwFull_pre : sliceNat wFull 0 (m * D) = encHist I (pre h_inf (m * D)) := by
              have hw_len : wFull.length = dep := by
                simp only [wFull, encHist, pre, List.length_map, List.length_ofFn]
              rw [sliceNat_eq_take_drop wFull 0 (m * D) (by omega)]
              apply List.ext_getElem
              · simp only [List.length_take, List.length_drop, hw_len, encHist, pre,
                  List.length_map, List.length_ofFn]
                omega
              · intro j hj1 hj2
                simp only [wFull, encHist, pre, List.getElem_take, List.getElem_drop,
                  List.getElem_map, List.getElem_ofFn, zero_add]
            have hwFull_suf : sliceNat wFull (m * D) (dep - m * D) = (uSeq m).take (t + 1) := by
              have hw_len : wFull.length = dep := by
                simp only [wFull, encHist, pre, List.length_map, List.length_ofFn]
              rw [sliceNat_eq_take_drop wFull (m * D) (dep - m * D) (by omega)]
              apply List.ext_getElem
              · simp only [List.length_take, List.length_drop, hw_len, uSeq, encBlock, encHist,
                  List.length_map, List.length_ofFn]
                omega
              · intro j hj1 hj2
                simp only [wFull, encHist, pre, uSeq, encBlock, toBlocks, List.getElem_take,
                  List.getElem_drop, List.getElem_map, List.getElem_ofFn]
            have htr_wFull : traceBlocksNat E ctx tpσ (sliceNat wFull 0 (((dep - 1) / D) * D)) =
                (true, addrFin.map Fin.val, idx) := by
              rw [hdiv_dep, hwFull_pre, hpre_blocks m]
              exact hfold_m
            have hcand_ev := hevalView_of_cand dep hdep1 wFull hwFull_in (addrFin.map Fin.val) idx htr_wFull
            rw [hdiv_dep, hwFull_suf, decHist_encHist] at hcand_ev
            let wi := cIdxOf words ((uSeq m).take (t + 1))
            have hwi_lt : wi < NW := by
              rw [cIdxOf_lt_iff_mem, mem_nonemptyExtWords_iff]
              refine ⟨by simp [uSeq, encBlock, encHist],
                by simp [uSeq, encBlock, encHist]; omega, ?_⟩
              intro x hx
              have hx' := List.mem_of_mem_take hx
              obtain ⟨_, hu_lt⟩ := (mem_fullBlocks_iff I D (uSeq m)).mp (huSeq_blk m)
              exact hu_lt x hx'
            have hrwi_lt : r * NW + wi < pa.1.1 * NW := by
              have h1 : r + 1 ≤ pa.1.1 := hr_lt
              calc r * NW + wi < r * NW + NW := Nat.add_lt_add_left hwi_lt _
                _ = (r + 1) * NW := by ring
                _ ≤ pa.1.1 * NW := Nat.mul_le_mul_right NW h1
            have ho1_lt : pa.2.2.1.getD (r * NW + wi) 0 < I.m1 + 1 := by
              rw [getD_eq_getElem pa.2.2.1 0 _ (hact_mem.2.2.1.symm ▸ hrwi_lt)]
              exact hact_mem.2.2.2.1 _ (List.getElem_mem _)
            have ho2_lt : pa.2.2.2.getD (r * NW + wi) 0 < I.m2 + 1 := by
              rw [getD_eq_getElem pa.2.2.2 0 _ (hact_mem.2.2.2.2.1.symm ▸ hrwi_lt)]
              exact hact_mem.2.2.2.2.2 _ (List.getElem_mem _)
            have ha_unfold : (E.unfoldLabelPacked tpσ (addrFin.map Fin.val)) % (labels.length + 1) =
                (tTree addrFin).val := by dsimp only [tTree]; rw [hts_len]
            have hc1_val : evalCandOutNat E ctx tpσ 0 (addrFin.map Fin.val) idx ((uSeq m).take (t + 1)) =
                pa.2.2.1.getD (r * NW + wi) 0 := by
              unfold evalCandOutNat
              rw [← hlabels_def]
              dsimp only [ctxI, ctxD, ctx]
              rw [ha_unfold, hpa_get, if_pos rfl, Nat.mod_eq_of_lt ho1_lt]
            have hc2_val : evalCandOutNat E ctx tpσ 1 (addrFin.map Fin.val) idx ((uSeq m).take (t + 1)) =
                pa.2.2.2.getD (r * NW + wi) 0 := by
              unfold evalCandOutNat
              rw [← hlabels_def]
              dsimp only [ctxI, ctxD, ctx]
              rw [ha_unfold, hpa_get, if_neg (by decide : (1 : ℕ) ≠ 0), Nat.mod_eq_of_lt ho2_lt]
            have he_tf : toBlocks D e m tf =
                (h_inf (m * D + t),
                  (f.f1 (view1 (pre h_inf dep)), f.f2 (view2 (pre h_inf dep)))) := rfl
            rw [hs_eq, hx1, hx2, hg, he_tf]
            dsimp only [f]
            rw [hcand_ev.1, hcand_ev.2, hc1_val, hc2_val]
        rw [hio_eq]
      let q' := symNextState E ctx pa.1 pa.2 r (uSeq m)
      have hlive_q' : (ctxLive ctx).getD q' false = true := by
        dsimp only [ctxLive, ctx, q']
        rw [hq'_eq]
        exact hlive_all (m + 1)
      -- Advance `foldBlocksNat E ctx tpσ ((List.range (m + 1)).map uSeq)`
      have hfold_succ : foldBlocksNat E ctx tpσ ((List.range (m + 1)).map uSeq) =
          traceStepNat E ctx tpσ (true, addrFin.map Fin.val, idx) (uSeq m) := by
        rw [List.range_succ, List.map_append, List.map_singleton, foldBlocksNat_snoc, hfold_m]
      unfold traceStepNat at hfold_succ
      rw [← hlabels_def] at hfold_succ
      dsimp only at hfold_succ
      have ha_unfold : (E.unfoldLabelPacked tpσ (addrFin.map Fin.val)) % (labels.length + 1) =
          (tTree addrFin).val := by dsimp only [tTree]; rw [hts_len]
      have hidx_pa : idx < pa.1.1 := hidx_lt
      rw [if_neg (by decide), ha_unfold, if_neg (by omega), hpa_get] at hfold_succ
      rw [if_neg (by omega), if_pos hlive_q'] at hfold_succ
      let comps := symComponents E ctx pa.1 pa.2
      let elem : SymExtElem := (r, uSeq m, q')
      let hits := findHitComps comps elem
      have hfold_succ1 : foldBlocksNat E ctx tpσ ((List.range (m + 1)).map uSeq) =
        (if hits.length = 0 then (false, [], 0)
         else (true, addrFin.map Fin.val ++ [hits.getD 0 0],
           cIdxOf (comps.getD (hits.getD 0 0) []) elem)) := by
        dsimp only [comps, elem, hits, q', r]; exact hfold_succ
      have hr_fix : r ∈ fixedIdxs pa.1 pa.2 := by
        simp only [fixedIdxs, List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨hr_lt, hr_idem idx hidx_lt⟩
      have helem_S : elem ∈ symLiveExts E ctx pa.1 pa.2 :=
        (mem_symLiveExts_iff E ctx pa.1 pa.2 elem).mpr ⟨hr_fix, huSeq_blk m, rfl, hlive_q'⟩
      obtain ⟨hs_lt, hs_get⟩ := cIdxOf_lt_and_getElem helem_S
      let sIdx := cIdxOf (symLiveExts E ctx pa.1 pa.2) elem
      have hex_comp : ∃ d0 < comps.length, cIdxOf (comps.getD d0 []) elem < (comps.getD d0 []).length := by
        let S := symLiveExts E ctx pa.1 pa.2
        let cIdxs := componentsIdx inhSymExt S (symExtAdj I pa.1)
        have hc_in : compIdxOf inhSymExt S (symExtAdj I pa.1) sIdx ∈ cIdxs := by
          dsimp only [cIdxs]
          unfold componentsIdx
          rw [mem_dedupList, List.mem_map]
          exact ⟨sIdx, List.mem_range.mpr hs_lt, rfl⟩
        obtain ⟨hd0_ci, hd0_get⟩ := cIdxOf_lt_and_getElem hc_in
        have hd0_lt : cIdxOf cIdxs (compIdxOf inhSymExt S (symExtAdj I pa.1) sIdx) < comps.length := by
          simpa [comps, symComponents, cIdxs, hctxI] using hd0_ci
        refine ⟨_, hd0_lt, ?_⟩
        rw [cIdxOf_lt_iff_mem, getD_eq_getElem comps [] _ hd0_lt]
        simp only [comps, symComponents, hctxI, List.getElem_map]
        change elem ∈ (cIdxs[cIdxOf cIdxs _]'hd0_ci).map _
        rw [hd0_get, List.mem_map]
        refine ⟨sIdx, (compIdxOf_nodup_and_lt inhSymExt S _ hs_lt).2.1, ?_⟩
        rw [getD_eq_getElem S inhSymExt sIdx hs_lt, hs_get]
      obtain ⟨d0, hd0_lt, hd0_in⟩ := hex_comp
      have hd0_hits : d0 ∈ hits := by
        simp only [hits, findHitComps, List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨hd0_lt, hd0_in⟩
      have hhits_ne : hits.length ≠ 0 := Nat.ne_of_gt (List.length_pos_of_mem hd0_hits)
      rw [if_neg hhits_ne] at hfold_succ1
      let d := hits.getD 0 0
      have hd_mem : d ∈ hits := by
        dsimp only [d]; rw [getD_eq_getElem hits 0 0 (by omega)]; exact List.getElem_mem _
      have hd_mem' : d < comps.length ∧ cIdxOf (comps.getD d []) elem < (comps.getD d []).length := by
        simpa only [hits, findHitComps, List.mem_filter, List.mem_range, decide_eq_true_eq] using hd_mem
      have hd_lt : d < comps.length := hd_mem'.1
      obtain ⟨hcomps_le, hcomp_all⟩ := symComponents_props E ctx pa.1 pa.2 hfix_le
      have hd_lt_B : d < B_full := lt_of_lt_of_le hd_lt hcomps_le
      have hd_lt_ts : d < ts.1 + 1 := by rw [hB_succ]; exact hd_lt_B
      let dFin : Fin (ts.1 + 1) := ⟨d, hd_lt_ts⟩
      let comp := comps[d]'hd_lt
      have helem_comp : elem ∈ comp := by
        have := hd_mem'.2
        rwa [cIdxOf_lt_iff_mem, getD_eq_getElem comps [] d hd_lt] at this
      obtain ⟨hj_lt, hj_get⟩ := cIdxOf_lt_and_getElem helem_comp
      let j := cIdxOf comp elem
      have hj_lt_B : j < B_full := lt_of_lt_of_le hj_lt (hcomp_all d hd_lt).2.1
      have hFin_d : dFin.val = d := by dsimp only [dFin]
      have hcomp_get : comps.getD d [] = comp := getD_eq_getElem comps [] d hd_lt
      have hcomp_raw : (symComponents E ctx pa.1 pa.2).getD d [] = comp := hcomp_get
      have hfold_succ' : foldBlocksNat E ctx tpσ ((List.range (m + 1)).map uSeq) =
          (true, (addrFin ++ [dFin]).map Fin.val, j) := by
        have hd_def : hits.getD 0 0 = d := rfl
        rw [hfold_succ1, hd_def, hcomp_get, List.map_append, List.map_singleton, hFin_d]
      -- Child node position and `stateAt`
      have hch_ok := hchild_ok addrFin dFin
      rw [tsChildOk_buildTreeSpec, ← hlabels_def, if_neg ha_ne, hpa_get, hFin_d] at hch_ok
      dsimp only at hch_ok
      rw [if_pos hd_lt] at hch_ok
      by_cases ha'_zero : (tTree (addrFin ++ [dFin])).val = 0
      · rw [if_pos ha'_zero] at hch_ok; cases hch_ok
      · rw [if_neg ha'_zero, decide_eq_true_eq, hctxI, hcomp_raw] at hch_ok
        refine ⟨addrFin ++ [dFin], j, hfold_succ', by simp [hlen_m], hj_lt_B, ?_, ?_⟩
        · rw [hch_ok, (childSymPos_access I pa.1 comp).2.2.2 j hj_lt, hj_get]
          exact hq'_eq
        · intro m0 hm0
          cases Nat.succ.inj hm0
          refine ⟨addrFin, dFin, idx, rfl, hfold_m, ?_⟩
          unfold edgeStepOk
          rw [if_neg ha_ne, if_pos ha_lt, hpa_get]
          dsimp only
          rw [if_pos hd_lt, hcomp_raw,
            if_pos ⟨hidx_lt, hj_lt⟩, getD_eq_getElem comp (0, [], 0) j hj_lt, hj_get]
          simp only [andBool_eq, Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨rfl, ?_⟩
          have hB_prio : ∀ s : Fin (res.1.1 + 1), B.prio s = res.1.2.2.getD s.val 0 := fun _ => rfl
          rw [hB_prio]
          dsimp only [elem, q', ctxBCode, ctx]
          rw [hq'_eq]
  -- Extract infinite branch `dSeq : ℕ → Fin (ts.1 + 1)` and index thread `iSeq : ℕ → Fin B_full`
  let addrAt : ℕ → List (Fin (ts.1 + 1)) := fun m => (htrack m).choose
  let idxAt : ℕ → ℕ := fun m => (htrack m).choose_spec.choose
  have htr_fold : ∀ m,
      foldBlocksNat E ctx tpσ ((List.range m).map uSeq) = (true, (addrAt m).map Fin.val, idxAt m) :=
    fun m => (htrack m).choose_spec.choose_spec.1
  have htr_len : ∀ m, (addrAt m).length = m :=
    fun m => (htrack m).choose_spec.choose_spec.2.1
  have htr_lt : ∀ m, idxAt m < B_full :=
    fun m => (htrack m).choose_spec.choose_spec.2.2.1
  have htr_step : ∀ m,
      ∃ (addrPrev : List (Fin (ts.1 + 1))) (dFin : Fin (ts.1 + 1)) (idxPrev : ℕ),
        addrAt (m + 1) = addrPrev ++ [dFin] ∧
        foldBlocksNat E ctx tpσ ((List.range m).map uSeq) = (true, addrPrev.map Fin.val, idxPrev) ∧
        edgeStepOk E ctx labels (tTree addrPrev).val dFin.val idxPrev
          (B.prio (B.run (toBlocks D e) (m + 1))) (idxAt (m + 1)) = true :=
    fun m => (htrack (m + 1)).choose_spec.choose_spec.2.2.2.2 m rfl
  let dSeq : ℕ → Fin (ts.1 + 1) :=
    fun m => (htr_step m).choose_spec.choose
  let iSeq : ℕ → Fin B_full :=
    fun m => ⟨idxAt m, htr_lt m⟩
  have haddr_eq_pre : ∀ m, addrAt m = List.ofFn (fun i : Fin m => dSeq i.val) := by
    intro m
    induction m with
    | zero =>
      exact List.eq_nil_of_length_eq_zero (htr_len 0)
    | succ m ih =>
      let stepSpec := htr_step m
      let addrPrev := stepSpec.choose
      let idxPrev := stepSpec.choose_spec.choose_spec.choose
      have hsp := stepSpec.choose_spec.choose_spec.choose_spec
      have happend : addrAt (m + 1) = addrPrev ++ [dSeq m] := hsp.1
      have hfold_prev : foldBlocksNat E ctx tpσ ((List.range m).map uSeq) =
          (true, addrPrev.map Fin.val, idxPrev) := hsp.2.1
      have hpair_eq : (true, (addrAt m).map Fin.val, idxAt m) =
          (true, addrPrev.map Fin.val, idxPrev) :=
        (htr_fold m).symm.trans hfold_prev
      have hmap_eq : (addrAt m).map Fin.val = addrPrev.map Fin.val :=
        (Prod.mk.inj (Prod.mk.inj hpair_eq).2).1
      have hprev_eq : addrPrev = addrAt m :=
        (List.map_injective_iff.mpr Fin.val_injective hmap_eq).symm
      rw [happend, hprev_eq, ih]
      apply List.ext_getElem
      · simp
      · intro k hk1 hk2
        simp only [List.length_append, List.length_ofFn, List.length_singleton] at hk1
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk1) with hlt | rfl
        · rw [List.getElem_append_left (by simp [hlt]), List.getElem_ofFn, List.getElem_ofFn]
        · rw [List.getElem_append_right (by simp), List.getElem_singleton, List.getElem_ofFn]
  have hi0 : (iSeq 0).val = 0 := by
    have hf0 := htr_fold 0
    simp only [foldBlocksNat, List.range_zero, List.map_nil, List.foldl_nil, Prod.mk.injEq] at hf0
    exact hf0.2.2.symm
  let K_prio := maxList res.1.2.2
  have hprio_le : ∀ n, B.prio (B.run (toBlocks D e) n) ≤ K_prio :=
    fun n => getD_zero_le_maxList res.1.2.2 (B.run (toBlocks D e) n).val
  let pSeq : ℕ → Fin (K_prio + 1) :=
    fun m => ⟨B.prio (B.run (toBlocks D e) (m + 1)), Nat.lt_succ_of_le (hprio_le (m + 1))⟩
  have hedge_all : ∀ m, edgeStepOk E ctx labels
      (tTree (List.ofFn (fun i : Fin m => dSeq i.val))).val (dSeq m).val
      (iSeq m).val (pSeq m).val (iSeq (m + 1)).val = true := by
    intro m
    let stepSpec := htr_step m
    let addrPrev := stepSpec.choose
    let idxPrev := stepSpec.choose_spec.choose_spec.choose
    have hsp := stepSpec.choose_spec.choose_spec.choose_spec
    have hfold_prev : foldBlocksNat E ctx tpσ ((List.range m).map uSeq) =
        (true, addrPrev.map Fin.val, idxPrev) := hsp.2.1
    have hok : edgeStepOk E ctx labels (tTree addrPrev).val (dSeq m).val idxPrev
        (pSeq m).val (iSeq (m + 1)).val = true := hsp.2.2
    have hpair_eq : (true, (addrAt m).map Fin.val, idxAt m) =
        (true, addrPrev.map Fin.val, idxPrev) :=
      (htr_fold m).symm.trans hfold_prev
    rcases Prod.mk.inj (Prod.mk.inj hpair_eq).2 with ⟨hmap_eq, hidx_eq⟩
    have hprev_eq : addrPrev = List.ofFn (fun i : Fin m => dSeq i.val) :=
      ((List.map_injective_iff.mpr Fin.val_injective hmap_eq).symm).trans (haddr_eq_pre m)
    have hidx_eq' : (iSeq m).val = idxPrev := hidx_eq
    rw [← hprev_eq, hidx_eq']
    exact hok
  have hno_odd := (tsDPA_buildTreeSpec_accepts_iff E ctx
    (fun m => (tTree (List.ofFn (fun i : Fin m => dSeq i.val)), dSeq m))).mp (hbranch_acc dSeq)
  rw [← hlabels_def] at hno_odd
  have hnot_odd : ¬ OddParityCond (fun m => (pSeq m).val) :=
    fun hodd => hno_odd ⟨iSeq, pSeq, hi0, hedge_all, hodd⟩
  have hpar_shift : ParityCond (fun m => B.prio (B.run (toBlocks D e) (1 + m))) := by
    have hp1 : ParityCond (fun m => (pSeq m).val) := by
      by_contra hnp
      exact hnot_odd ((oddParityCond_iff_not_parityCond_of_bdd _ K_prio
        (fun m => hprio_le (m + 1))).mpr hnp)
    simpa [pSeq, Nat.add_comm 1] using hp1
  have hB_acc : B.Accepts (toBlocks D e) := (parityCond_shift _ 1).mpr hpar_shift
  rcases (hB.accepts e).mp hB_acc with hnotA | hsat
  · exact False.elim (hnotA (hge_eq ▸ hg_in_A))
  · exact hsat

def solveCtxBool (E : Thm34Engine) (ctx : SymCtx) : Bool :=
  if (ctxLive ctx).getD 0 false = false then true
  else
    match E.solveTreePG (buildTreeSpec E ctx) with
    | none => false
    | some _ => true

lemma primrec_solveCtxBool (E : Thm34Engine) : Primrec (solveCtxBool E) := by
  have hlive0 : Primrec fun ctx : SymCtx => (ctxLive ctx).getD 0 false :=
    (Primrec.list_getD false).comp primrec_ctxLive (Primrec.const 0)
  have hsol : Primrec fun ctx : SymCtx => E.solveTreePG (buildTreeSpec E ctx) :=
    E.primrec_solveTreePG.comp (primrec_buildTreeSpec E)
  have hisSome : Primrec fun ctx : SymCtx =>
      match E.solveTreePG (buildTreeSpec E ctx) with
      | none => false
      | some _ => true :=
    (Primrec.option_casesOn hsol (Primrec.const false) (Primrec.const true).to₂).of_eq fun ctx => by
      cases E.solveTreePG (buildTreeSpec E ctx) <;> rfl
  exact (Primrec.ite (Primrec.eq.comp hlive0 (Primrec.const false))
    (Primrec.const true) hisSome).of_eq fun _ => rfl

def evalCtxAlgo (E : Thm34Engine) (ctx : SymCtx) (x : ℕ) : ℕ :=
  if (ctxLive ctx).getD 0 false = false then 0
  else
    let ts := buildTreeSpec E ctx
    match E.solveTreePG ts with
    | none => 0
    | some σ =>
      let tpσ := Nat.pair (E.packTS ts) (Encodable.encode σ)
      evalViewPacked E ctx (Nat.pair tpσ x)

lemma primrec₂_evalCtxAlgo (E : Thm34Engine) : Primrec₂ (evalCtxAlgo E) := by
  let Q := SymCtx × ℕ
  have hlive0 : Primrec fun q : Q => (ctxLive q.1).getD 0 false :=
    (Primrec.list_getD false).comp (primrec_ctxLive.comp Primrec.fst) (Primrec.const 0)
  have hts : Primrec fun q : Q => buildTreeSpec E q.1 :=
    (primrec_buildTreeSpec E).comp Primrec.fst
  have hsol : Primrec fun q : Q => E.solveTreePG (buildTreeSpec E q.1) :=
    E.primrec_solveTreePG.comp hts
  have hsome : Primrec fun r : Q × List ℕ =>
      let tpσ := Nat.pair (E.packTS (buildTreeSpec E r.1.1)) (Encodable.encode r.2)
      evalViewPacked E r.1.1 (Nat.pair tpσ r.1.2) := by
    have rtpσ : Primrec fun r : Q × List ℕ =>
        Nat.pair (E.packTS (buildTreeSpec E r.1.1)) (Encodable.encode r.2) :=
      primrec₂_natPair.comp (E.primrec_packTS.comp (hts.comp Primrec.fst))
        (Primrec.encode.comp Primrec.snd)
    exact (primrec₂_evalViewPacked E).comp (Primrec.fst.comp Primrec.fst)
      (primrec₂_natPair.comp rtpσ (Primrec.snd.comp Primrec.fst))
  have hmatch : Primrec fun q : Q =>
      match E.solveTreePG (buildTreeSpec E q.1) with
      | none => 0
      | some σ =>
        let tpσ := Nat.pair (E.packTS (buildTreeSpec E q.1)) (Encodable.encode σ)
        evalViewPacked E q.1 (Nat.pair tpσ q.2) :=
    (Primrec.option_casesOn hsol (Primrec.const 0) hsome.to₂).of_eq fun q => by
      cases E.solveTreePG (buildTreeSpec E q.1) <;> rfl
  exact (Primrec.ite (Primrec.eq.comp hlive0 (Primrec.const false))
    (Primrec.const 0) hmatch).of_eq fun _ => rfl

def ctxOf (E : Thm34Engine) (D_fn : DPACode → ℕ) (p : DPACode × Instance) : SymCtx :=
  let D_m1 := D_fn p.1 - 1
  let res := E.compileBlock (p.1, p.2, D_m1)
  (p.2, D_m1, res.1, res.2)

lemma computable_ctxOf (E : Thm34Engine) {D_fn : DPACode → ℕ} (hD : Computable D_fn) :
    Computable (ctxOf E D_fn) := by
  have hDm1 : Computable fun p : DPACode × Instance => D_fn p.1 - 1 :=
    Primrec.nat_sub.to_comp.comp (hD.comp Computable.fst) (Computable.const 1)
  have hres : Computable fun p : DPACode × Instance => E.compileBlock (p.1, p.2, D_fn p.1 - 1) :=
    E.primrec_compileBlock.to_comp.comp (Computable.fst.pair (Computable.snd.pair hDm1))
  exact Computable.snd.pair (hDm1.pair ((Computable.fst.comp hres).pair (Computable.snd.comp hres)))

def decOf (E : Thm34Engine) (D_fn : DPACode → ℕ) (p : DPACode × Instance) : Bool :=
  if parseOk p.2.tokens = false then false
  else solveCtxBool E (ctxOf E D_fn p)

lemma computable_decOf (E : Thm34Engine) {D_fn : DPACode → ℕ} (hD : Computable D_fn) :
    Computable (decOf E D_fn) := by
  have hpOk : Computable fun p : DPACode × Instance => decide (parseOk p.2.tokens = false) :=
    (primrec_decide (Primrec.eq.comp (primrec_parseOk.comp (primrec_instTokens.comp Primrec.snd))
      (Primrec.const false))).to_comp
  exact (Computable.cond hpOk (Computable.const false)
    ((primrec_solveCtxBool E).to_comp.comp (computable_ctxOf E hD))).of_eq fun p => by
    unfold decOf; by_cases h : parseOk p.2.tokens = false <;> simp [h]

def runAlgo (E : Thm34Engine) (D_fn : DPACode → ℕ) (px : (DPACode × Instance) × ℕ) : ℕ :=
  if parseOk px.1.2.tokens = false then 0
  else evalCtxAlgo E (ctxOf E D_fn px.1) px.2

lemma computable_runAlgo (E : Thm34Engine) {D_fn : DPACode → ℕ} (hD : Computable D_fn) :
    Computable (runAlgo E D_fn) := by
  have hpOk : Computable fun px : (DPACode × Instance) × ℕ => decide (parseOk px.1.2.tokens = false) :=
    (primrec_decide (Primrec.eq.comp (primrec_parseOk.comp (primrec_instTokens.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.const false))).to_comp
  have hev : Computable fun px : (DPACode × Instance) × ℕ => evalCtxAlgo E (ctxOf E D_fn px.1) px.2 :=
    (primrec₂_evalCtxAlgo E).to_comp.comp ((computable_ctxOf E hD).comp Computable.fst) Computable.snd
  exact (Computable.cond hpOk (Computable.const 0) hev).of_eq fun px => by
    unfold runAlgo; by_cases h : parseOk px.1.2.tokens = false <;> simp [h]

theorem theorem_3_4_of_engine (E : Thm34Engine) :
    ∃ dec : DPACode × Instance → Bool, Computable dec ∧
      ∃ con : DPACode × Instance → Nat.Partrec.Code, Computable con ∧
        ∀ (c : DPACode) (I : Instance), IsNowhereDense (piMap '' c.lang) →
          (dec (c, I) = true ↔ I.Realizable c.lang) ∧
            (I.Realizable c.lang → I.RealizedByCode c.lang (con (c, I))) := by
  obtain ⟨D_fn, hD_comp, hD_spec⟩ := lemma_3_6 Bool (by decide)
  obtain ⟨con, hcon_comp, hcon_eval⟩ := exists_curried_code (computable_runAlgo E hD_comp)
  refine ⟨decOf E D_fn, computable_decOf E hD_comp, con, hcon_comp, ?_⟩
  intro c I hnd
  by_cases hp : parseOk I.tokens = false
  · have hno_parse : ∀ φ, parse I.tokens ≠ some φ := by
      intro φ hφ
      have ht := (parseOk_iff_exists_parse I.tokens).mpr ⟨φ, hφ⟩
      rw [hp] at ht; cases ht
    have hnot_real : ¬ I.Realizable c.lang := by
      rintro ⟨φ, hφ, _⟩; exact hno_parse φ hφ
    exact ⟨⟨fun hd => by simp [decOf, hp] at hd, fun hr => False.elim (hnot_real hr)⟩,
      fun hr => False.elim (hnot_real hr)⟩
  · have hp_true : parseOk I.tokens = true := Bool.eq_true_of_not_eq_false hp
    obtain ⟨φ, hparse⟩ := (parseOk_iff_exists_parse I.tokens).mp hp_true
    obtain ⟨hD_ge1, hCons_raw⟩ := hD_spec c hnd
    let D_m1 := D_fn c - 1
    let D := D_m1 + 1
    have hD_eq : D = D_fn c := Nat.sub_add_cancel hD_ge1
    have hCons : ∀ g ∈ Pref c.lang, ConsensusSolvableWithin Bool (leftQuot g c.lang) (D_m1 + 1) := by
      simpa [D, hD_eq] using hCons_raw
    let res := E.compileBlock (c, I, D_m1)
    let ctx : SymCtx := (I, D_m1, res.1, res.2)
    let dpa := toGenDPA (E.blockAlphaMinusOne I D) res.1
    let B : DPA (Fin (res.1.1 + 1)) (Fin D → Signal I.X1 I.X2 × (I.Y1 × I.Y2)) :=
      ⟨dpa.init, fun q blk => dpa.step q (E.encIOBlockTyped I D blk), dpa.prio⟩
    let Qlive : Set (Fin (res.1.1 + 1)) := {q | res.2.getD q.val false = true}
    have hB : IsBlockAutomaton c.lang (instFormulaOf I φ) D B Qlive :=
      E.compileBlock_spec c I D_m1 φ hparse
    have hlive0_iff : res.2.getD 0 false = true ↔ ([] : List CommGraph) ∈ Pref c.lang :=
      reachableInB_live hB (reachableInB_zero B)
    by_cases hl0 : res.2.getD 0 false = false
    · -- Empty adversary `c.lang = ∅`
      have hnot_pref0 : ([] : List CommGraph) ∉ Pref c.lang := by
        intro hm; have := hlive0_iff.mpr hm; rw [hl0] at this; cases this
      have hempty : ∀ w, w ∉ c.lang := by
        intro w hw
        exact hnot_pref0 ⟨w, hw, by simp [pre]⟩
      let f0 : Algorithm I.X1 I.X2 I.Y1 I.Y2 :=
        { f1 := fun _ => ⟨0, Nat.succ_pos _⟩
          f2 := fun _ => ⟨0, Nat.succ_pos _⟩ }
      have hf0_real : RealizesLang f0 c.lang (I.Lang φ) :=
        fun h hh => False.elim (hempty (graphOf h) hh)
      have hctx_eq : ctxOf E D_fn (c, I) = ctx := rfl
      have hl_ctx : (ctxLive ctx).getD 0 false = false := hl0
      have hf0_code : CodeComputes (con (c, I)) f0 := by
        intro v
        constructor
        · rw [hcon_eval]
          dsimp only [runAlgo]
          rw [if_neg hp, hctx_eq]
          dsimp only [evalCtxAlgo]
          rw [if_pos hl_ctx]
          simp [f0, encode_fin_val]
        · rw [hcon_eval]
          dsimp only [runAlgo]
          rw [if_neg hp, hctx_eq]
          dsimp only [evalCtxAlgo]
          rw [if_pos hl_ctx]
          simp [f0, encode_fin_val]
      exact ⟨⟨fun _ => ⟨φ, hparse, f0, hf0_real⟩,
        fun _ => by
          unfold decOf
          rw [if_neg hp, hctx_eq]
          unfold solveCtxBool
          rw [if_pos hl_ctx]⟩,
        fun _ => ⟨φ, hparse, f0, hf0_code, hf0_real⟩⟩
    · -- Nonempty adversary `[] ∈ Pref c.lang`
      have hl0_true : res.2.getD 0 false = true := Bool.eq_true_of_not_eq_false hl0
      have hlive0 : ([] : List CommGraph) ∈ Pref c.lang := hlive0_iff.mp hl0_true
      let ts := buildTreeSpec E ctx
      have hreal_to_sol : I.Realizable c.lang → E.solveTreePG ts ≠ none := by
        rintro ⟨φ', hparse', f, hf_lang⟩
        have hφ_eq : φ' = φ := Option.some.inj (hparse'.symm.trans hparse)
        subst hφ_eq
        have hf_real : FRealizes f c.lang (instFormulaOf I φ') :=
          (fRealizes_instFormulaOf_iff I φ' c.lang f).mpr hf_lang
        obtain ⟨t0, ht0, hacc0⟩ :=
          (lemma_3_9 c.lang (instFormulaOf I φ') D (Nat.succ_pos D_m1) B Qlive hB).1.mp ⟨f, hf_real⟩
        exact uncomp_implies_solveTreePG_ne_none E c I D_m1 φ' hparse hCons hlive0 t0 ht0 hacc0
      have hsol_to_code : ∀ σ, E.solveTreePG ts = some σ →
          I.Realizable c.lang ∧ I.RealizedByCode c.lang (con (c, I)) := by
        intro σ hsol
        let tpσ := Nat.pair (E.packTS ts) (Encodable.encode σ)
        let fσ : Algorithm I.X1 I.X2 I.Y1 I.Y2 :=
          { f1 := fun v => ⟨evalViewPacked E ctx (Nat.pair tpσ (Nat.pair 0 (Encodable.encode v))),
              (evalViewPacked_lt E ctx tpσ (Encodable.encode v)).1⟩
            f2 := fun v => ⟨evalViewPacked E ctx (Nat.pair tpσ (Nat.pair 1 (Encodable.encode v))),
              (evalViewPacked_lt E ctx tpσ (Encodable.encode v)).2⟩ }
        have hfσ_freal : FRealizes fσ c.lang (instFormulaOf I φ) :=
          soundness_of_solveTreePG_some E c I D_m1 φ hparse σ hsol
        have hfσ_lang : RealizesLang fσ c.lang (I.Lang φ) :=
          (fRealizes_instFormulaOf_iff I φ c.lang fσ).mp hfσ_freal
        have hfσ_code : CodeComputes (con (c, I)) fσ := by
          intro v
          have hctx_eq : ctxOf E D_fn (c, I) = ctx := rfl
          have hl_ctx : (ctxLive ctx).getD 0 false = true := hl0_true
          constructor
          · rw [hcon_eval]
            dsimp only [runAlgo]
            rw [if_neg hp, hctx_eq]
            dsimp only [evalCtxAlgo]
            rw [if_neg (by rw [hl_ctx]; decide)]
            change Part.some (match E.solveTreePG ts with
                | none => 0
                | some σ' => evalViewPacked E ctx (Nat.pair (Nat.pair (E.packTS ts) (Encodable.encode σ'))
                    (Nat.pair 0 (Encodable.encode v)))) = _
            rw [hsol]
            simp [fσ, tpσ, encode_fin_val]
          · rw [hcon_eval]
            dsimp only [runAlgo]
            rw [if_neg hp, hctx_eq]
            dsimp only [evalCtxAlgo]
            rw [if_neg (by rw [hl_ctx]; decide)]
            change Part.some (match E.solveTreePG ts with
                | none => 0
                | some σ' => evalViewPacked E ctx (Nat.pair (Nat.pair (E.packTS ts) (Encodable.encode σ'))
                    (Nat.pair 1 (Encodable.encode v)))) = _
            rw [hsol]
            simp [fσ, tpσ, encode_fin_val]
        exact ⟨⟨φ, hparse, fσ, hfσ_lang⟩, ⟨φ, hparse, fσ, hfσ_code, hfσ_lang⟩⟩
      constructor
      · constructor
        · intro hdec
          unfold decOf at hdec
          rw [if_neg hp] at hdec
          have hctx_eq : ctxOf E D_fn (c, I) = ctx := rfl
          rw [hctx_eq] at hdec
          unfold solveCtxBool at hdec
          have hl_ctx : (ctxLive ctx).getD 0 false = true := hl0_true
          rw [if_neg (by rw [hl_ctx]; decide)] at hdec
          cases hsol : E.solveTreePG ts with
          | none =>
            change (match E.solveTreePG ts with | none => false | some _ => true) = true at hdec
            rw [hsol] at hdec; cases hdec
          | some σ =>
            exact (hsol_to_code σ hsol).1
        · intro hreal
          have hne := hreal_to_sol hreal
          cases hsol : E.solveTreePG ts with
          | none => exact False.elim (hne hsol)
          | some σ =>
            unfold decOf
            rw [if_neg hp]
            have hctx_eq : ctxOf E D_fn (c, I) = ctx := rfl
            rw [hctx_eq]
            unfold solveCtxBool
            have hl_ctx : (ctxLive ctx).getD 0 false = true := hl0_true
            rw [if_neg (by rw [hl_ctx]; decide)]
            change (match E.solveTreePG ts with | none => false | some _ => true) = true
            rw [hsol]
      · intro hreal
        have hne := hreal_to_sol hreal
        cases hsol : E.solveTreePG ts with
        | none => exact False.elim (hne hsol)
        | some σ => exact (hsol_to_code σ hsol).2

end DistLTLSynth.Char.Thm34Aux

open DistLTLSynth.Char DistLTLSynth.Char.Thm34Aux in
theorem solution :
    ∃ dec : DPACode × Instance → Bool, Computable dec ∧
      ∃ con : DPACode × Instance → Nat.Partrec.Code, Computable con ∧
        ∀ (c : DPACode) (I : Instance), IsNowhereDense (piMap '' c.lang) →
          (dec (c, I) = true ↔ I.Realizable c.lang) ∧
            (I.Realizable c.lang → I.RealizedByCode c.lang (con (c, I))) := by
  obtain ⟨hdetNBW, detListNBW, hprim_detList, hcorr_detList⟩ := nbw_determinization
  obtain ⟨solveTreePG, packTS, unfoldLabelPacked, hprim_solve, hprim_pack, hprim_unfold,
    hsound_solve, hiff_solve⟩ := regular_tree_parity_solver
  obtain ⟨blockAlphaMinusOne, encIOBlockNat, encIOBlockTyped, compileBlock,
    hprim_alpha, hprim_encNat, hcompat_enc, hprim_comp, hspec_comp⟩ := lemma_3_7 hdetNBW
  exact theorem_3_4_of_engine
    { detListNBW := detListNBW
      primrec_detListNBW := hprim_detList
      detListNBW_accepts_iff := hcorr_detList
      solveTreePG := solveTreePG
      packTS := packTS
      unfoldLabelPacked := unfoldLabelPacked
      primrec_solveTreePG := hprim_solve
      primrec_packTS := hprim_pack
      primrec₂_unfoldLabelPacked := hprim_unfold
      solveTreePG_some_sound := hsound_solve
      solveTreePG_iff_exists_tree := hiff_solve
      blockAlphaMinusOne := blockAlphaMinusOne
      primrec_blockAlphaMinusOne := hprim_alpha
      encIOBlockNat := encIOBlockNat
      primrec_encIOBlockNat := hprim_encNat
      encIOBlockTyped := encIOBlockTyped
      encIOBlock_compat := hcompat_enc
      compileBlock := compileBlock
      primrec_compileBlock := hprim_comp
      compileBlock_spec := hspec_comp }

