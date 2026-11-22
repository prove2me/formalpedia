-- Prove2me | solution 1 for DistLTLSynth.Char.nbw_determinization
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T09:13:34.618099+00:00
-- url     : https://prove2.me/submissions/49d75df4-efe6-479c-8256-b3dc3a072d26

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL
import Definitions.Def_DistLTLSynth_Char_Automata
import Definitions.Def_DistLTLSynth_Char_ComponentTree
import Definitions.Def_DistLTLSynth_Char_SynthesisEngine

set_option autoImplicit false

namespace DistLTLSynth.Char.Thm34NBWAux

open DistLTLSynth.Char

/-! ### Section 1: Encoded DPAs, Encoded NBWs, and Primitive-Recursive Combinators -/

/-- Finite description of a deterministic parity automaton over `Fin (αSize + 1)`:
`(maxState, trans, prios)` describes the automaton with state space `Fin (d.1 + 1)`,
initial state `0`, transition `step s a = trans[s * (αSize + 1) + a] mod (d.1 + 1)`,
and priority `prio s = prios[s]` (missing entries default to `0`). -/
abbrev GenDPACode : Type := ℕ × List ℕ × List ℕ

/-- Semantic deterministic parity automaton over `Fin (αSize + 1)` decoded from `d`. -/
def toGenDPA (αSize : ℕ) (d : GenDPACode) : DPA (Fin (d.1 + 1)) (Fin (αSize + 1)) where
  init := ⟨0, Nat.succ_pos _⟩
  step s a := ⟨(d.2.1.getD (s.val * (αSize + 1) + a.val) 0) % (d.1 + 1),
    Nat.mod_lt _ (Nat.succ_pos _)⟩
  prio s := d.2.2.getD s.val 0

/-- List-based description of a nondeterministic Büchi automaton over `Fin (αSize + 1)`:
`(maxState, initList, transRows, accList)` describes the NBW with state space `Fin (B.1 + 1)`,
initial states `{q | q.val ∈ B.2.1}`, transitions
`q' ∈ delta q a ↔ q'.val ∈ B.2.2.1.getD ((αSize + 1) * q.val + a.val) []`,
and accepting states `{q | q.val ∈ B.2.2.2}`. -/
abbrev ListNBWCode : Type := ℕ × List ℕ × List (List ℕ) × List ℕ

/-- Acceptance of an infinite word `w : ℕ → Fin (αSize + 1)` by a `ListNBWCode` `B`. -/
def ListNBWAccepts (αSize : ℕ) (B : ListNBWCode) (w : ℕ → Fin (αSize + 1)) : Prop :=
  ∃ ρ : ℕ → Fin (B.1 + 1),
    (ρ 0).val ∈ B.2.1 ∧
    (∀ n, (ρ (n + 1)).val ∈ B.2.2.1.getD ((αSize + 1) * (ρ n).val + (w n).val) []) ∧
    ∃ q : Fin (B.1 + 1), q.val ∈ B.2.2.2 ∧ ∃ᶠ n in Filter.atTop, ρ n = q

lemma exists_inf_state_of_frequently {S : ℕ} (P : Fin S → Prop) (ρ : ℕ → Fin S)
    (hfreq : ∃ᶠ n in Filter.atTop, P (ρ n)) :
    ∃ q : Fin S, P q ∧ ∃ᶠ n in Filter.atTop, ρ n = q := by
  by_contra hno
  have hall : ∀ q : Fin S, ∀ᶠ n in Filter.atTop, ¬ (P q ∧ ρ n = q) := by
    intro q
    by_cases hq : P q
    · have hnf : ¬ ∃ᶠ n in Filter.atTop, ρ n = q := fun hf => hno ⟨q, hq, hf⟩
      rw [Filter.not_frequently] at hnf
      exact hnf.mono fun n hn h => hn h.2
    · exact Filter.Eventually.of_forall fun _ h => hq h.1
  have hev : ∀ᶠ n in Filter.atTop, ¬ P (ρ n) :=
    (Filter.eventually_all.mpr hall).mono fun n hn hp => hn (ρ n) ⟨hp, rfl⟩
  exact (Filter.not_frequently.mpr hev) hfreq

lemma ListNBWAccepts_iff_frequently (αSize : ℕ) (B : ListNBWCode) (w : ℕ → Fin (αSize + 1)) :
    ListNBWAccepts αSize B w ↔
      ∃ ρ : ℕ → Fin (B.1 + 1),
        (ρ 0).val ∈ B.2.1 ∧
        (∀ n, (ρ (n + 1)).val ∈ B.2.2.1.getD ((αSize + 1) * (ρ n).val + (w n).val) []) ∧
        ∃ᶠ n in Filter.atTop, (ρ n).val ∈ B.2.2.2 := by
  constructor
  · rintro ⟨ρ, h0, hstep, q, hq, hfreq⟩
    exact ⟨ρ, h0, hstep, hfreq.mono fun n hn => hn ▸ hq⟩
  · rintro ⟨ρ, h0, hstep, hfreq⟩
    obtain ⟨q, hq, hqfreq⟩ :=
      exists_inf_state_of_frequently (fun q : Fin (B.1 + 1) => q.val ∈ B.2.2.2) ρ hfreq
    exact ⟨ρ, h0, hstep, q, hq, hqfreq⟩

/-! #### Basic primitive-recursive combinators -/

lemma primrec₂_natPair : Primrec₂ Nat.pair := Primrec.encode

def cMax (a b : ℕ) : ℕ := if a ≤ b then b else a

lemma primrec₂_cMax : Primrec₂ cMax :=
  Primrec.ite Primrec.nat_le Primrec.snd Primrec.fst

lemma cMax_eq_max (a b : ℕ) : cMax a b = max a b := by
  unfold cMax
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (Nat.le_of_not_le h)).symm

def minWith (fallback : ℕ) (xs : List ℕ) : ℕ :=
  xs.foldr min fallback

lemma primrec₂_minWith : Primrec₂ minWith :=
  Primrec.list_foldr Primrec.snd Primrec.fst
    (Primrec.nat_min.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

lemma le_minWith_iff (k fallback : ℕ) (xs : List ℕ) :
    k ≤ minWith fallback xs ↔ k ≤ fallback ∧ ∀ r ∈ xs, k ≤ r := by
  induction xs with
  | nil => simp [minWith]
  | cons x xs ih =>
    change k ≤ min x (minWith fallback xs) ↔ k ≤ fallback ∧ ∀ r ∈ x :: xs, k ≤ r
    rw [le_min_iff, ih, List.forall_mem_cons]
    tauto

lemma minWith_le_fallback (fallback : ℕ) (xs : List ℕ) : minWith fallback xs ≤ fallback :=
  ((le_minWith_iff _ _ _).mp le_rfl).1

lemma minWith_le_of_mem (fallback : ℕ) (xs : List ℕ) {r : ℕ} (hr : r ∈ xs) :
    minWith fallback xs ≤ r :=
  ((le_minWith_iff _ _ _).mp le_rfl).2 r hr

def maxList (xs : List ℕ) : ℕ :=
  xs.foldr cMax 0

lemma primrec_maxList : Primrec maxList :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (primrec₂_cMax.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

lemma maxList_eq_foldr_max (xs : List ℕ) : maxList xs = xs.foldr max 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change cMax x (maxList xs) = max x (xs.foldr max 0)
    rw [cMax_eq_max, ih]

lemma le_maxList_of_mem {xs : List ℕ} {x : ℕ} (hx : x ∈ xs) : x ≤ maxList xs := by
  rw [maxList_eq_foldr_max]
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact le_max_left _ _
    · exact le_trans (ih hmem) (le_max_right _ _)

lemma list_product_primrec {α β : Type} [Primcodable α] [Primcodable β] :
    Primrec₂ (List.product (α := α) (β := β)) :=
  Primrec.list_flatMap Primrec.fst
    (Primrec.list_map (Primrec.snd.comp Primrec.fst)
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂).to₂

lemma mem_list_product_iff {α β : Type} {l1 : List α} {l2 : List β} {a : α} {b : β} :
    (a, b) ∈ l1.product l2 ↔ a ∈ l1 ∧ b ∈ l2 := by
  simp [List.product]

lemma list_sublists_primrec {α : Type} [Primcodable α] :
    Primrec (List.sublists' (α := α)) := by
  have hf : Primrec (fun xs : List α => xs.foldr
      (fun a tails => tails ++ tails.map (List.cons a)) [[]]) :=
    Primrec.list_foldr Primrec.id (Primrec.const [[]])
      (Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.list_map (Primrec.snd.comp Primrec.snd)
          (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
            Primrec.snd).to₂)).to₂
  exact hf.of_eq (fun xs => by
    induction xs <;> simp_all [List.sublists'_cons, List.sublists'_nil])

lemma list_sections_primrec {α : Type} [Primcodable α] :
    Primrec (List.sections (α := α)) := by
  have hf : Primrec (fun xs : List (List α) => xs.foldr
      (fun choices tails => tails.flatMap (fun tail => choices.map (fun a => a :: tail))) [[]]) :=
    Primrec.list_foldr Primrec.id (Primrec.const [[]])
      (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd)
        (Primrec.list_map (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂).to₂).to₂
  exact hf.of_eq (fun xs => by induction xs <;> simp_all [List.sections])

def wordsOf {α : Type} (choices : List α) (n : ℕ) : List (List α) :=
  ((List.range n).map (fun _ => choices)).sections

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

lemma exists_mem_primrec {X α : Type} [Primcodable X] [Primcodable α]
    {xs : X → List α} {p : X × α → Prop}
    (hxs : Primrec xs) (hp : PrimrecPred p) :
    PrimrecPred (fun x => ∃ a ∈ xs x, p (x, a)) := by
  have hrel : PrimrecRel (fun x a => p (x, a)) := hp
  exact hrel.swap.exists_mem_list.comp hxs Primrec.id

lemma exists_lt_primrec {X : Type} [Primcodable X] {bound : X → ℕ} {p : X × ℕ → Prop}
    (hb : Primrec bound) (hp : PrimrecPred p) :
    PrimrecPred (fun x => ∃ i < bound x, p (x, i)) := by
  have hrel : PrimrecRel (fun x i => p (x, i)) := hp
  exact (hrel.swap.exists_mem_list.comp (Primrec.list_range.comp hb) Primrec.id).of_eq (by simp)

lemma filter_primrec {X α : Type} [Primcodable X] [Primcodable α]
    {xs : X → List α} {p : X × α → Prop} [DecidablePred p]
    (hxs : Primrec xs) (hp : PrimrecPred p) :
    Primrec (fun x => (xs x).filter (fun a => decide (p (x, a)))) := by
  have hrel : PrimrecRel (fun x a => p (x, a)) := hp
  exact hrel.swap.listFilter.comp hxs Primrec.id

lemma mem_list_primrec {α : Type} [Primcodable α] [DecidableEq α] :
    PrimrecRel (fun (a : α) (xs : List α) => a ∈ xs) :=
  (Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)).swap

/-! #### `DecidableEq`-based deduplication and index lookup (avoiding `BEq` diamonds) -/

def dedupRight {α : Type} [DecidableEq α] (xs : List α) : List α :=
  xs.foldr (fun x ys => if x ∈ ys then ys else x :: ys) []

lemma mem_dedupRight {α : Type} [DecidableEq α] (xs : List α) (a : α) :
    a ∈ dedupRight xs ↔ a ∈ xs := by
  induction xs generalizing a with
  | nil => simp [dedupRight]
  | cons x xs ih =>
    change a ∈ (if x ∈ dedupRight xs then dedupRight xs else x :: dedupRight xs) ↔ a ∈ x :: xs
    split_ifs with h
    · have hx := (ih x).mp h
      simp only [ih, List.mem_cons]
      exact ⟨Or.inr, fun hc => hc.elim (fun he => he ▸ hx) id⟩
    · simp only [List.mem_cons, ih]

lemma nodup_dedupRight {α : Type} [DecidableEq α] (xs : List α) : (dedupRight xs).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    change (if x ∈ dedupRight xs then dedupRight xs else x :: dedupRight xs).Nodup
    split_ifs with h
    · exact ih
    · exact List.nodup_cons.mpr ⟨h, ih⟩

lemma dedupRight_primrec {α : Type} [Primcodable α] [DecidableEq α] :
    Primrec (dedupRight (α := α)) :=
  Primrec.list_foldr Primrec.id (Primrec.const [])
    (Primrec.ite
      (mem_list_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))).to₂

def dedupLeft {α : Type} [DecidableEq α] (xs : List α) : List α :=
  (dedupRight xs.reverse).reverse

lemma mem_dedupLeft {α : Type} [DecidableEq α] (xs : List α) (a : α) :
    a ∈ dedupLeft xs ↔ a ∈ xs := by
  simp [dedupLeft, mem_dedupRight]

lemma nodup_dedupLeft {α : Type} [DecidableEq α] (xs : List α) : (dedupLeft xs).Nodup := by
  simpa [dedupLeft] using List.nodup_reverse.mpr (nodup_dedupRight xs.reverse)

lemma dedupLeft_primrec {α : Type} [Primcodable α] [DecidableEq α] :
    Primrec (dedupLeft (α := α)) :=
  Primrec.list_reverse.comp (dedupRight_primrec.comp Primrec.list_reverse)

lemma dedupRight_append_singleton {α : Type} [DecidableEq α] (ys : List α) (x : α) :
    ∃ pre, dedupRight (ys ++ [x]) = pre ++ [x] := by
  induction ys with
  | nil => exact ⟨[], rfl⟩
  | cons y ys ih =>
    obtain ⟨pre, hpre⟩ := ih
    have hstep : dedupRight (y :: (ys ++ [x])) =
        if y ∈ dedupRight (ys ++ [x]) then dedupRight (ys ++ [x])
        else y :: dedupRight (ys ++ [x]) := rfl
    rw [List.cons_append, hstep]
    split_ifs
    · exact ⟨pre, hpre⟩
    · exact ⟨y :: pre, by simp [hpre]⟩

lemma dedupLeft_cons_head {α : Type} [DecidableEq α] (x : α) (xs : List α) :
    ∃ rest, dedupLeft (x :: xs) = x :: rest := by
  unfold dedupLeft
  rw [List.reverse_cons]
  obtain ⟨pre, hpre⟩ := dedupRight_append_singleton xs.reverse x
  exact ⟨pre.reverse, by simp [hpre]⟩

lemma dedupLeft_cons_pos {α : Type} [DecidableEq α] (x : α) (xs : List α) :
    0 < (dedupLeft (x :: xs)).length := by
  obtain ⟨rest, hrest⟩ := dedupLeft_cons_head x xs
  simp [hrest]

/-- First-index lookup using `DecidableEq`. Returns `xs.length` if absent. -/
def cIdxOf {α : Type} [DecidableEq α] (xs : List α) (x : α) : ℕ :=
  xs.foldr (fun y acc => if y = x then 0 else acc + 1) 0

lemma cIdxOf_nil {α : Type} [DecidableEq α] (x : α) : cIdxOf ([] : List α) x = 0 := rfl

lemma cIdxOf_cons {α : Type} [DecidableEq α] (y : α) (ys : List α) (x : α) :
    cIdxOf (y :: ys) x = if y = x then 0 else cIdxOf ys x + 1 := rfl

lemma cIdxOf_primrec {α : Type} [Primcodable α] [DecidableEq α] :
    Primrec₂ (cIdxOf (α := α)) :=
  Primrec.list_foldr Primrec.fst (Primrec.const 0)
    (Primrec.ite
      (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
      (Primrec.const 0)
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))).to₂

lemma cIdxOf_lt_length_of_mem {α : Type} [DecidableEq α] {xs : List α} {x : α} (h : x ∈ xs) :
    cIdxOf xs x < xs.length := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    rw [cIdxOf_cons]
    split_ifs with hyx
    · simp
    · rcases List.mem_cons.mp h with rfl | hmem
      · exact absurd rfl hyx
      · simp [ih hmem]

lemma getElem_cIdxOf_of_mem {α : Type} [DecidableEq α] {xs : List α} {x : α} (h : x ∈ xs) :
    xs[cIdxOf xs x]'(cIdxOf_lt_length_of_mem h) = x := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    simp only [cIdxOf_cons]
    split_ifs with hyx
    · simp [hyx]
    · rcases List.mem_cons.mp h with rfl | hmem
      · exact absurd rfl hyx
      · simpa [hyx] using ih hmem

lemma getD_cIdxOf_of_mem {α : Type} [DecidableEq α] {xs : List α} {x : α} (d : α) (h : x ∈ xs) :
    xs.getD (cIdxOf xs x) d = x := by
  rw [List.getD_eq_getElem _ _ (cIdxOf_lt_length_of_mem h), getElem_cIdxOf_of_mem h]

lemma cIdxOf_getElem_of_nodup {α : Type} [DecidableEq α] {xs : List α} (hnodup : xs.Nodup)
    (i : ℕ) (hi : i < xs.length) : cIdxOf xs xs[i] = i := by
  induction xs generalizing i with
  | nil => cases hi
  | cons y ys ih =>
    obtain ⟨hynot, hys⟩ := List.nodup_cons.mp hnodup
    cases i with
    | zero => simp [cIdxOf_cons]
    | succ j =>
      have hj : j < ys.length := Nat.lt_of_succ_lt_succ hi
      have hne : y ≠ ys[j] := fun heq => hynot (heq ▸ List.getElem_mem hj)
      simp [cIdxOf_cons, hne, ih hys j hj]

lemma cIdxOf_dedupLeft_head {α : Type} [DecidableEq α] (x : α) (xs : List α) :
    cIdxOf (dedupLeft (x :: xs)) x = 0 := by
  obtain ⟨rest, hrest⟩ := dedupLeft_cons_head x xs
  simp [hrest, cIdxOf_cons]

/-! #### Flat state-major transition table lookup helpers -/

lemma flatMap_range_getD {S A : ℕ} (f : ℕ → ℕ → ℕ) {s a : ℕ} (hs : s < S) (ha : a < A) :
    ((List.range S).flatMap (fun q => (List.range A).map (f q))).getD (A * s + a) 0 = f s a := by
  induction S with
  | zero => omega
  | succ m ih =>
    have hlen_pre : ((List.range m).flatMap (fun q => (List.range A).map (f q))).length = A * m := by
      clear ih hs
      induction m with
      | zero => simp
      | succ k ihk => simp [List.range_succ, ihk, Nat.mul_add]
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hs) with hlt | heq
    · have hidx : A * s + a < A * m := by
        have : s + 1 ≤ m := hlt
        calc A * s + a < A * s + A := by omega
          _ = A * (s + 1) := by ring
          _ ≤ A * m := Nat.mul_le_mul_left A this
      have hidx' : A * s + a < ((List.range m).flatMap (fun q => (List.range A).map (f q))).length := by
        rwa [hlen_pre]
      have htot : A * s + a <
          (((List.range m).flatMap (fun q => (List.range A).map (f q))) ++
            (List.range A).map (f m)).length := by
        rw [List.length_append]; omega
      rw [List.getD_eq_getElem _ _ htot, List.getElem_append_left hidx',
        ← List.getD_eq_getElem _ 0 hidx']
      exact ih hlt
    · subst s
      have hge : ((List.range m).flatMap (fun q => (List.range A).map (f q))).length ≤ A * m + a := by
        rw [hlen_pre]; omega
      have htot : A * m + a <
          (((List.range m).flatMap (fun q => (List.range A).map (f q))) ++
            (List.range A).map (f m)).length := by
        rw [List.length_append, hlen_pre, List.length_map, List.length_range]; omega
      rw [List.getD_eq_getElem _ _ htot, List.getElem_append_right hge]
      simp [hlen_pre]

lemma flatMap_range_getD_list {S A : ℕ} (f : ℕ → ℕ → List ℕ) {s a : ℕ} (hs : s < S) (ha : a < A) :
    ((List.range S).flatMap (fun q => (List.range A).map (f q))).getD (A * s + a) [] = f s a := by
  induction S with
  | zero => omega
  | succ m ih =>
    have hlen_pre : ((List.range m).flatMap (fun q => (List.range A).map (f q))).length = A * m := by
      clear ih hs
      induction m with
      | zero => simp
      | succ k ihk => simp [List.range_succ, ihk, Nat.mul_add]
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hs) with hlt | heq
    · have hidx : A * s + a < A * m := by
        have : s + 1 ≤ m := hlt
        calc A * s + a < A * s + A := by omega
          _ = A * (s + 1) := by ring
          _ ≤ A * m := Nat.mul_le_mul_left A this
      have hidx' : A * s + a < ((List.range m).flatMap (fun q => (List.range A).map (f q))).length := by
        rwa [hlen_pre]
      have htot : A * s + a <
          (((List.range m).flatMap (fun q => (List.range A).map (f q))) ++
            (List.range A).map (f m)).length := by
        rw [List.length_append]; omega
      rw [List.getD_eq_getElem _ _ htot, List.getElem_append_left hidx',
        ← List.getD_eq_getElem _ [] hidx']
      exact ih hlt
    · subst s
      have hge : ((List.range m).flatMap (fun q => (List.range A).map (f q))).length ≤ A * m + a := by
        rw [hlen_pre]; omega
      have htot : A * m + a <
          (((List.range m).flatMap (fun q => (List.range A).map (f q))) ++
            (List.range A).map (f m)).length := by
        rw [List.length_append, hlen_pre, List.length_map, List.length_range]; omega
      rw [List.getD_eq_getElem _ _ htot, List.getElem_append_right hge]
      simp [hlen_pre]

lemma map_range_getD {S : ℕ} (f : ℕ → ℕ) {s : ℕ} (hs : s < S) :
    ((List.range S).map f).getD s 0 = f s := by
  have hlen : s < ((List.range S).map f).length := by simp [hs]
  rw [List.getD_eq_getElem _ _ hlen]
  simp

/-! #### Canonical finite-subset codes -/

def normalizeSet (n : ℕ) (xs : List ℕ) : List ℕ :=
  (List.range n).filter (fun q => decide (q ∈ xs))

def decodeSet (n : ℕ) (xs : List ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun q : Fin n => q.val ∈ xs)

def encodeSet {n : ℕ} (s : Finset (Fin n)) : List ℕ :=
  (List.range n).filter (fun q => decide (∃ h : q < n, (⟨q, h⟩ : Fin n) ∈ s))

def codesSet (n : ℕ) : List (List ℕ) :=
  (List.range n).sublists'

lemma normalizeSet_primrec : Primrec₂ normalizeSet :=
  mem_list_primrec.listFilter.comp (Primrec.list_range.comp Primrec.fst) Primrec.snd

lemma codesSet_primrec : Primrec codesSet :=
  list_sublists_primrec.comp Primrec.list_range

@[simp] lemma mem_decodeSet (n : ℕ) (xs : List ℕ) (q : Fin n) :
    q ∈ decodeSet n xs ↔ q.val ∈ xs := by
  simp [decodeSet]

@[simp] lemma mem_normalizeSet (n q : ℕ) (xs : List ℕ) :
    q ∈ normalizeSet n xs ↔ q < n ∧ q ∈ xs := by
  simp [normalizeSet]

lemma decodeSet_normalizeSet (n : ℕ) (xs : List ℕ) :
    decodeSet n (normalizeSet n xs) = decodeSet n xs := by
  ext q; simp [q.isLt]

lemma normalizeSet_eq_iff (n : ℕ) (xs ys : List ℕ) :
    normalizeSet n xs = normalizeSet n ys ↔ decodeSet n xs = decodeSet n ys := by
  constructor
  · intro h
    simpa only [decodeSet_normalizeSet] using congrArg (decodeSet n) h
  · intro h
    apply List.filter_congr
    intro q hq
    have he := Finset.ext_iff.mp h ⟨q, List.mem_range.mp hq⟩
    simp only [mem_decodeSet] at he
    simp [he]

lemma normalizeSet_idem (n : ℕ) (xs : List ℕ) :
    normalizeSet n (normalizeSet n xs) = normalizeSet n xs :=
  (normalizeSet_eq_iff _ _ _).mpr (decodeSet_normalizeSet _ _)

lemma decodeSet_encodeSet {n : ℕ} (s : Finset (Fin n)) :
    decodeSet n (encodeSet s) = s := by
  ext q; simp [encodeSet, q.isLt]

lemma normalizeSet_encodeSet {n : ℕ} (s : Finset (Fin n)) :
    normalizeSet n (encodeSet s) = encodeSet s := by
  simp only [normalizeSet, encodeSet]
  apply List.filter_congr
  intro q hq
  simp [List.mem_range.mp hq]

lemma encodeSet_mem_codesSet {n : ℕ} (s : Finset (Fin n)) :
    encodeSet s ∈ codesSet n :=
  List.mem_sublists'.mpr List.filter_sublist

lemma normalizeSet_eq_nil_iff (n : ℕ) (xs : List ℕ) :
    normalizeSet n xs = [] ↔ decodeSet n xs = ∅ := by
  have hnil : normalizeSet n [] = [] := by simp [normalizeSet]
  have hd : decodeSet n [] = ∅ := by ext q; simp
  simpa only [hnil, hd] using normalizeSet_eq_iff n xs []

/-! ### Section 2: Schewe History-Tree NBW Determinization + Index Appearance Record -/

abbrev Node : Type := List ℕ

section SemanticHistory
noncomputable section
open scoped Classical

/-! #### Semantic NBW and History-Tree structures -/

structure SemNBW (Q Sigma : Type) where
  initial : Finset Q
  delta : Q → Sigma → Finset Q
  accepting : Finset Q

def infSet {X : Type} (f : ℕ → X) : Set X := {x | ∀ N, ∃ i ≥ N, f i = x}

def IsRun {Q Sigma : Type} (B : SemNBW Q Sigma) (α : ℕ → Sigma) (ρ : ℕ → Q) : Prop :=
  ρ 0 ∈ B.initial ∧ ∀ i, ρ (i + 1) ∈ B.delta (ρ i) (α i)

def semLanguage {Q Sigma : Type} (B : SemNBW Q Sigma) : Set (ℕ → Sigma) :=
  {α | ∃ ρ, IsRun B α ρ ∧ ∃ q ∈ B.accepting, q ∈ infSet ρ}

def toSemNBW (αSize : ℕ) (B : ListNBWCode) : SemNBW (Fin (B.1 + 1)) (Fin (αSize + 1)) where
  initial := decodeSet (B.1 + 1) B.2.1
  delta q a := decodeSet (B.1 + 1) (B.2.2.1.getD ((αSize + 1) * q.val + a.val) [])
  accepting := decodeSet (B.1 + 1) B.2.2.2

lemma mem_semLanguage_toSemNBW (αSize : ℕ) (B : ListNBWCode) (w : ℕ → Fin (αSize + 1)) :
    w ∈ semLanguage (toSemNBW αSize B) ↔ ListNBWAccepts αSize B w := by
  unfold semLanguage IsRun toSemNBW ListNBWAccepts infSet
  simp only [Set.mem_ofPred, mem_decodeSet, Filter.frequently_atTop, and_assoc]

def Positive (x : Node) : Prop := ∀ i ∈ x, 0 < i

def Ordered (T : Finset Node) : Prop :=
  (∀ x ∈ T, Positive x) ∧
  (∀ x ∈ T, ∀ p, p.IsPrefix x → p ∈ T) ∧
  (∀ p i, p ++ [i] ∈ T → ∀ j, 0 < j → j ≤ i → p ++ [j] ∈ T)

def children (T : Finset Node) (x : Node) : Finset Node :=
  T.filter fun y => ∃ i, y = x ++ [i]

def degree (T : Finset Node) (x : Node) : ℕ :=
  ((children T x).image fun y => y.getLast!).sup id

structure TreeData (Q : Type) where
  nodes : Finset Node
  label : Node → Finset Q

def childLabels {Q : Type} (H : TreeData Q) (x : Node) : Finset Q :=
  (children H.nodes x).biUnion H.label

def own {Q : Type} (H : TreeData Q) (x : Node) : Finset Q :=
  H.label x \ childLabels H x

def Valid {Q : Type} (H : TreeData Q) : Prop :=
  Ordered H.nodes ∧ [] ∈ H.nodes ∧
  (∀ x, x ∉ H.nodes → H.label x = ∅) ∧
  (∀ x ∈ H.nodes, (H.label x).Nonempty) ∧
  (∀ p i j, p ++ [i] ∈ H.nodes → p ++ [j] ∈ H.nodes → i ≠ j →
    Disjoint (H.label (p ++ [i])) (H.label (p ++ [j]))) ∧
  (∀ x ∈ H.nodes, childLabels H x ⊂ H.label x)

abbrev History (Q : Type) := {H : TreeData Q // Valid H}

def asHistory {Q : Type} (H : TreeData Q) : Option (History Q) :=
  if h : Valid H then some ⟨H, h⟩ else none

def initialData {Q Sigma : Type} (B : SemNBW Q Sigma) : TreeData Q :=
  ⟨{[]}, fun x => if x = [] then B.initial else ∅⟩

def initialHistory {Q Sigma : Type} (B : SemNBW Q Sigma) : Option (History Q) :=
  asHistory (initialData B)

def expand {Q Sigma : Type} (B : SemNBW Q Sigma) (H : TreeData Q) (σ : Sigma) : TreeData Q :=
  let next := fun x => (H.label x).biUnion fun q => B.delta q σ
  let T := H.nodes ∪ H.nodes.image (fun x => x ++ [degree H.nodes x + 1])
  ⟨T, fun x => if x ∈ H.nodes then next x else
    if x ∈ T then next x.dropLast ∩ B.accepting else ∅⟩

def horizontal {Q : Type} (H : TreeData Q) : TreeData Q :=
  ⟨H.nodes, fun x => (H.label x).filter fun q =>
    ¬ ∃ p i v j, x = p ++ i :: v ∧ 0 < j ∧ j < i ∧
      p ++ [j] ∈ H.nodes ∧ q ∈ H.label (p ++ [j])⟩

def removeEmpty {Q : Type} (H : TreeData Q) : TreeData Q :=
  let T := H.nodes.filter fun x => (H.label x).Nonempty
  ⟨T, fun x => if x ∈ T then H.label x else ∅⟩

def resetNodes {Q : Type} (H : TreeData Q) : Finset Node :=
  H.nodes.filter fun x => H.label x = childLabels H x

def prune {Q : Type} (H : TreeData Q) : TreeData Q :=
  let T := H.nodes.filter fun x =>
    ¬ ∃ p ∈ resetNodes H, p.IsPrefix x ∧ p ≠ x
  ⟨T, fun x => if x ∈ T then H.label x else ∅⟩

def compress (T : Finset Node) (x : Node) : Node :=
  (List.range x.length).map fun k =>
    (T.filter fun y => ∃ j, y = x.take k ++ [j] ∧ j < x[k]!).card + 1

def compressed {Q : Type} (H : TreeData Q) : TreeData Q :=
  ⟨H.nodes.image (compress H.nodes), fun x =>
    (H.nodes.filter fun y => compress H.nodes y = x).biUnion H.label⟩

def stage3 {Q Sigma : Type} (B : SemNBW Q Sigma) (H : TreeData Q) (σ : Sigma) : TreeData Q :=
  removeEmpty (horizontal (expand B H σ))

def stage4 {Q Sigma : Type} (B : SemNBW Q Sigma) (H : TreeData Q) (σ : Sigma) : TreeData Q :=
  prune (stage3 B H σ)

def successor {Q Sigma : Type} (B : SemNBW Q Sigma) (H : History Q) (σ : Sigma) :
    Option (History Q) :=
  asHistory (compressed (stage4 B H.val σ))

def unstable {Q Sigma : Type} (B : SemNBW Q Sigma) (H : History Q) (σ : Sigma) : Finset Node :=
  let K := stage4 B H.val σ
  H.val.nodes.filter fun x => x ∉ K.nodes ∨ compress K.nodes x ≠ x

def acceptingNodes {Q Sigma : Type} (B : SemNBW Q Sigma) (H : History Q) (σ : Sigma) :
    Finset Node :=
  let K := stage4 B H.val σ
  H.val.nodes.filter fun x => x ∈ resetNodes (stage3 B H.val σ) ∧
    x ∈ K.nodes ∧ compress K.nodes x = x

def IsTrace {Q Sigma : Type} (B : SemNBW Q Sigma) (α : ℕ → Sigma) (ρ : ℕ → History Q) : Prop :=
  initialHistory B = some (ρ 0) ∧ ∀ i, successor B (ρ i) (α i) = some (ρ (i + 1))

/-! #### Soundness and Completeness of Schewe History Trees -/

lemma getLast!_concat : ∀ (x : Node) (i : ℕ), (x ++ [i]).getLast! = i
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: b :: xs, i => getLast!_concat (b :: xs) i

lemma dropLast_concat : ∀ (x : Node) (i : ℕ), (x ++ [i]).dropLast = x
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: xs, i => congrArg (a :: ·) (dropLast_concat (b :: xs) i)

lemma append_singleton_inj {x y : Node} {i j : ℕ} (h : x ++ [i] = y ++ [j]) : x = y ∧ i = j := by
  have hx : x = y := by
    have := congrArg List.dropLast h
    rwa [dropLast_concat, dropLast_concat] at this
  subst hx
  exact ⟨rfl, by simpa using h⟩

lemma eq_of_prefix_of_length_eq {a b : Node} (h : a.IsPrefix b) (hl : a.length = b.length) :
    a = b := by
  obtain ⟨t, rfl⟩ := h
  have ht0 : t.length = 0 := by simp only [List.length_append] at hl; omega
  rcases List.eq_nil_of_length_eq_zero ht0 with rfl
  simp

lemma prefix_of_proper_prefix_concat {p x : Node} {i : ℕ}
    (hp : p.IsPrefix (x ++ [i])) (hne : p ≠ x ++ [i]) : p.IsPrefix x := by
  have hlen : p.length ≤ x.length := by
    have h1 := hp.length_le
    simp only [List.length_append, List.length_singleton] at h1
    by_cases h2 : p.length = x.length + 1
    · exact absurd (eq_of_prefix_of_length_eq hp (by simp [h2])) hne
    · omega
  obtain ⟨t, ht⟩ := hp
  have htk := congrArg (List.take p.length) ht
  rw [List.take_left, List.take_append_of_le_length hlen] at htk
  rw [htk]
  exact List.take_prefix _ _

lemma le_degree_of_mem {T : Finset Node} {x : Node} {i : ℕ} (h : x ++ [i] ∈ T) :
    i ≤ degree T x := by
  unfold degree
  have hch : x ++ [i] ∈ children T x := by simp [children, h]
  have himg : i ∈ (children T x).image (fun y => y.getLast!) :=
    Finset.mem_image.mpr ⟨x ++ [i], hch, getLast!_concat x i⟩
  exact Finset.le_sup (f := id) himg

lemma not_mem_succ_degree (T : Finset Node) (x : Node) :
    x ++ [degree T x + 1] ∉ T := by
  intro h; have := le_degree_of_mem h; omega

lemma mem_degree_of_pos {T : Finset Node} {x : Node} (hpos : 0 < degree T x) :
    x ++ [degree T x] ∈ T := by
  have hne : ((children T x).image (fun y => y.getLast!)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    unfold degree at hpos; rw [hemp] at hpos; simp at hpos
  obtain ⟨m, hm_mem, hm_eq⟩ := Finset.exists_mem_eq_sup _ hne id
  have hdeg : degree T x = m := hm_eq
  rw [hdeg]
  obtain ⟨y, hy_ch, hy_last⟩ := Finset.mem_image.mp hm_mem
  simp only [children, Finset.mem_filter] at hy_ch
  obtain ⟨hyT, j, rfl⟩ := hy_ch
  rw [getLast!_concat] at hy_last
  rwa [← hy_last]

lemma label_sub_of_prefix {Q : Type} {H : TreeData Q} (hv : Valid H) :
    ∀ (x : Node) (w : List ℕ), x ++ w ∈ H.nodes → H.label (x ++ w) ⊆ H.label x
  | x, [], _ => by simp
  | x, i :: rest, hmem => by
    have hxi_mem : x ++ [i] ∈ H.nodes :=
      hv.1.2.1 (x ++ (i :: rest)) hmem (x ++ [i]) ⟨rest, by simp⟩
    have h1 : H.label ((x ++ [i]) ++ rest) ⊆ H.label (x ++ [i]) :=
      label_sub_of_prefix hv (x ++ [i]) rest (by simpa using hmem)
    have h1' : H.label (x ++ i :: rest) ⊆ H.label (x ++ [i]) := by simpa using h1
    have hchild : x ++ [i] ∈ children H.nodes x := by simp [children, hxi_mem]
    have h2 : H.label (x ++ [i]) ⊆ childLabels H x :=
      Finset.subset_biUnion_of_mem H.label hchild
    have h3 : childLabels H x ⊆ H.label x :=
      (hv.2.2.2.2.2 x (hv.1.2.1 _ hxi_mem x ⟨[i], rfl⟩)).subset
    exact h1'.trans (h2.trans h3)

lemma split_incomparable :
    ∀ (x y : List ℕ), ¬ x.IsPrefix y → ¬ y.IsPrefix x →
      ∃ p i j u v, i ≠ j ∧ x = p ++ i :: u ∧ y = p ++ j :: v
  | [], _, hxy, _ => absurd List.nil_prefix hxy
  | _, [], _, hyx => absurd List.nil_prefix hyx
  | a :: xs, b :: ys, hxy, hyx => by
    by_cases hab : a = b
    · subst hab
      have hxy' : ¬ xs.IsPrefix ys := fun h => hxy (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
      have hyx' : ¬ ys.IsPrefix xs := fun h => hyx (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
      obtain ⟨p, i, j, u, v, hij, h1, h2⟩ := split_incomparable xs ys hxy' hyx'
      exact ⟨a :: p, i, j, u, v, hij, by simp [h1], by simp [h2]⟩
    · exact ⟨[], a, b, xs, ys, hab, rfl, rfl⟩

lemma own_disjoint {Q : Type} {H : TreeData Q} (hv : Valid H)
    {x y : Node} (hx : x ∈ H.nodes) (hy : y ∈ H.nodes) (hne : x ≠ y) :
    Disjoint (own H x) (own H y) := by
  rw [Finset.disjoint_left]
  intro q hqx hqy
  by_cases hpre1 : x.IsPrefix y
  · obtain ⟨w, rfl⟩ := hpre1
    cases w with
    | nil => exact hne (by simp)
    | cons i rest =>
      have hxi : x ++ [i] ∈ H.nodes := hv.1.2.1 _ hy (x ++ [i]) ⟨rest, by simp⟩
      have hsub : H.label ((x ++ [i]) ++ rest) ⊆ H.label (x ++ [i]) :=
        label_sub_of_prefix hv (x ++ [i]) rest (by simpa using hy)
      have hqy' : q ∈ H.label ((x ++ [i]) ++ rest) := by simpa using (Finset.mem_sdiff.mp hqy).1
      have hch : q ∈ childLabels H x :=
        Finset.mem_biUnion.mpr ⟨x ++ [i], by simp [children, hxi], hsub hqy'⟩
      exact (Finset.mem_sdiff.mp hqx).2 hch
  · by_cases hpre2 : y.IsPrefix x
    · obtain ⟨w, rfl⟩ := hpre2
      cases w with
      | nil => exact hne (by simp)
      | cons i rest =>
        have hyi : y ++ [i] ∈ H.nodes := hv.1.2.1 _ hx (y ++ [i]) ⟨rest, by simp⟩
        have hsub : H.label ((y ++ [i]) ++ rest) ⊆ H.label (y ++ [i]) :=
          label_sub_of_prefix hv (y ++ [i]) rest (by simpa using hx)
        have hqx' : q ∈ H.label ((y ++ [i]) ++ rest) := by simpa using (Finset.mem_sdiff.mp hqx).1
        have hch : q ∈ childLabels H y :=
          Finset.mem_biUnion.mpr ⟨y ++ [i], by simp [children, hyi], hsub hqx'⟩
        exact (Finset.mem_sdiff.mp hqy).2 hch
    · obtain ⟨p, i, j, u, v, hij, rfl, rfl⟩ := split_incomparable x y hpre1 hpre2
      have hpi : p ++ [i] ∈ H.nodes := hv.1.2.1 _ hx (p ++ [i]) ⟨u, by simp⟩
      have hpj : p ++ [j] ∈ H.nodes := hv.1.2.1 _ hy (p ++ [j]) ⟨v, by simp⟩
      have hqx' : q ∈ H.label ((p ++ [i]) ++ u) := by simpa using (Finset.mem_sdiff.mp hqx).1
      have hqy' : q ∈ H.label ((p ++ [j]) ++ v) := by simpa using (Finset.mem_sdiff.mp hqy).1
      have h1 : q ∈ H.label (p ++ [i]) :=
        label_sub_of_prefix hv (p ++ [i]) u (by simpa using hx) hqx'
      have h2 : q ∈ H.label (p ++ [j]) :=
        label_sub_of_prefix hv (p ++ [j]) v (by simpa using hy) hqy'
      exact Finset.disjoint_left.mp (hv.2.2.2.2.1 p i j hpi hpj hij) h1 h2

lemma nodes_card_le {Q : Type} [Fintype Q] (H : History Q) :
    H.val.nodes.card ≤ Fintype.card Q := by
  have hv := H.property
  have hdisj : (H.val.nodes : Set Node).PairwiseDisjoint (own H.val) :=
    fun x hx y hy hne => own_disjoint hv hx hy hne
  have hpos : ∀ x ∈ H.val.nodes, 1 ≤ (own H.val x).card := by
    intro x hx
    rw [Finset.one_le_card]
    have hss := hv.2.2.2.2.2 x hx
    rw [own, Finset.sdiff_nonempty]
    exact fun h => hss.not_subset h
  calc H.val.nodes.card
      = ∑ _x ∈ H.val.nodes, 1 := by simp
    _ ≤ ∑ x ∈ H.val.nodes, (own H.val x).card := Finset.sum_le_sum hpos
    _ = (H.val.nodes.biUnion (own H.val)).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.univ : Finset Q).card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card Q := Finset.card_univ

lemma length_lt_card_of_mem {Q : Type} [Fintype Q] (H : History Q)
    {p : Node} (hp : p ∈ H.val.nodes) : p.length < Fintype.card Q := by
  let S := (Finset.range (p.length + 1)).image (fun k => p.take k)
  have hsub : S ⊆ H.val.nodes := by
    intro u hu
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hu
    exact H.property.1.2.1 p hp (p.take k) (List.take_prefix k p)
  have hinj : Set.InjOn (fun k => p.take k) (Finset.range (p.length + 1)) := by
    intro k1 hk1 k2 hk2 heq
    simp only [Finset.mem_coe, Finset.mem_range] at hk1 hk2
    have hl := congrArg List.length heq
    rw [List.length_take_of_le (by omega), List.length_take_of_le (by omega)] at hl
    exact hl
  have hcardS : S.card = p.length + 1 := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hle : S.card ≤ Fintype.card Q :=
    (Finset.card_le_card hsub).trans (nodes_card_le H)
  omega

lemma entry_le_card_of_mem {Q : Type} [Fintype Q] (H : History Q)
    {x : Node} (hx : x ∈ H.val.nodes) {i : ℕ} (hi : i ∈ x) :
    0 < i ∧ i ≤ Fintype.card Q := by
  have hi0 : 0 < i := H.property.1.1 x hx i hi
  obtain ⟨p, rest, rfl⟩ := List.append_of_mem hi
  have hpi : p ++ [i] ∈ H.val.nodes := H.property.1.2.1 _ hx (p ++ [i]) ⟨rest, by simp⟩
  let S := (Finset.Icc 1 i).image (fun j => p ++ [j])
  have hsub : S ⊆ H.val.nodes := by
    intro u hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
    rw [Finset.mem_Icc] at hj
    exact H.property.1.2.2 p i hpi j hj.1 hj.2
  have hinj : Function.Injective (fun j : ℕ => p ++ [j]) :=
    fun _ _ h => (append_singleton_inj h).2
  have hcardS : S.card = i := by
    rw [Finset.card_image_of_injective _ hinj, Nat.card_Icc]
    omega
  have hle : S.card ≤ Fintype.card Q :=
    (Finset.card_le_card hsub).trans (nodes_card_le H)
  exact ⟨hi0, by omega⟩

lemma exists_own_of_mem_label {Q : Type} {H : TreeData Q} (_hv : Valid H)
    {u : Node} (hu : u ∈ H.nodes) {q : Q} (hq : q ∈ H.label u) :
    ∃ x ∈ H.nodes, u.IsPrefix x ∧ q ∈ own H x := by
  let S := H.nodes.filter (fun z => u.IsPrefix z ∧ q ∈ H.label z)
  have huS : u ∈ S := Finset.mem_filter.mpr ⟨hu, List.prefix_refl u, hq⟩
  obtain ⟨x, hxS, hm_sup⟩ := Finset.exists_mem_eq_sup S ⟨u, huS⟩ List.length
  have hx_mem : x ∈ H.nodes := (Finset.mem_filter.mp hxS).1
  have hux : u.IsPrefix x := (Finset.mem_filter.mp hxS).2.1
  have hqx : q ∈ H.label x := (Finset.mem_filter.mp hxS).2.2
  refine ⟨x, hx_mem, hux, Finset.mem_sdiff.mpr ⟨hqx, ?_⟩⟩
  intro hch
  obtain ⟨y, hy_ch, hqy⟩ := Finset.mem_biUnion.mp hch
  simp only [children, Finset.mem_filter] at hy_ch
  obtain ⟨hy_mem, j, rfl⟩ := hy_ch
  have huy : u.IsPrefix (x ++ [j]) := hux.trans ⟨[j], rfl⟩
  have hyS : x ++ [j] ∈ S := Finset.mem_filter.mpr ⟨hy_mem, huy, hqy⟩
  have hle : (x ++ [j]).length ≤ S.sup List.length := Finset.le_sup (f := List.length) hyS
  rw [hm_sup] at hle
  simp at hle

lemma mem_label_iff_prefix_own {Q : Type} {H : TreeData Q} (hv : Valid H)
    {x u : Node} {q : Q} (hx : x ∈ H.nodes) (hown : q ∈ own H x) (hu : u ∈ H.nodes) :
    q ∈ H.label u ↔ u.IsPrefix x := by
  constructor
  · intro hqu
    obtain ⟨y, hy, huy, hown_y⟩ := exists_own_of_mem_label hv hu hqu
    have hyx : y = x := by
      by_contra hne
      exact Finset.disjoint_left.mp (own_disjoint hv hy hx hne) hown_y hown
    rwa [← hyx]
  · rintro ⟨w, rfl⟩
    exact label_sub_of_prefix hv u w hx (Finset.mem_sdiff.mp hown).1

lemma expand_mem_iff {Q Sigma : Type} (B : SemNBW Q Sigma) (H : TreeData Q) (σ : Sigma) (y : Node) :
    y ∈ (expand B H σ).nodes ↔
      y ∈ H.nodes ∨ ∃ x ∈ H.nodes, y = x ++ [degree H.nodes x + 1] := by
  simp only [expand, Finset.mem_union, Finset.mem_image]
  exact or_congr_right ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩⟩

lemma expand_label_old {Q Sigma : Type} (B : SemNBW Q Sigma) (H : TreeData Q) (σ : Sigma)
    {x : Node} (hx : x ∈ H.nodes) :
    (expand B H σ).label x = (H.label x).biUnion (fun q => B.delta q σ) := by
  simp [expand, hx]

lemma expand_label_new {Q Sigma : Type} (B : SemNBW Q Sigma) (H : TreeData Q) (σ : Sigma)
    {x : Node} (hx : x ∈ H.nodes) :
    (expand B H σ).label (x ++ [degree H.nodes x + 1]) =
      ((H.label x).biUnion (fun q => B.delta q σ)) ∩ B.accepting := by
  have hnot : x ++ [degree H.nodes x + 1] ∉ H.nodes := not_mem_succ_degree H.nodes x
  have hmem : x ++ [degree H.nodes x + 1] ∈ (expand B H σ).nodes := by
    rw [expand_mem_iff]; exact Or.inr ⟨x, hx, rfl⟩
  unfold expand
  simp only [hnot, ↓reduceIte, dropLast_concat]
  rw [if_pos (by simpa [expand] using hmem)]

lemma expand_label_outside {Q Sigma : Type} (B : SemNBW Q Sigma) (H : TreeData Q) (σ : Sigma)
    {y : Node} (hy : y ∉ (expand B H σ).nodes) :
    (expand B H σ).label y = ∅ := by
  have hyH : y ∉ H.nodes := fun hm => hy ((expand_mem_iff B H σ y).mpr (Or.inl hm))
  unfold expand
  dsimp only
  rw [if_neg hyH, if_neg (by simpa [expand] using hy)]

lemma expand_ordered {Q Sigma : Type} (B : SemNBW Q Sigma) {H : TreeData Q}
    (hord : Ordered H.nodes) (σ : Sigma) :
    Ordered (expand B H σ).nodes := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    rcases (expand_mem_iff B H σ y).mp hy with hyH | ⟨x, hxH, rfl⟩
    · exact hord.1 y hyH
    · intro k hk
      rcases List.mem_append.mp hk with hkx | hkd
      · exact hord.1 x hxH k hkx
      · simp at hkd; omega
  · intro y hy p hp
    rcases (expand_mem_iff B H σ y).mp hy with hyH | ⟨x, hxH, rfl⟩
    · rw [expand_mem_iff]; exact Or.inl (hord.2.1 y hyH p hp)
    · by_cases hpeq : p = x ++ [degree H.nodes x + 1]
      · subst hpeq; exact hy
      · rw [expand_mem_iff]
        exact Or.inl (hord.2.1 x hxH p (prefix_of_proper_prefix_concat hp hpeq))
  · intro p i hpi j hj0 hjle
    rcases (expand_mem_iff B H σ (p ++ [i])).mp hpi with hpiH | ⟨x, hxH, heq⟩
    · rw [expand_mem_iff]; exact Or.inl (hord.2.2 p i hpiH j hj0 hjle)
    · obtain ⟨rfl, rfl⟩ := append_singleton_inj heq
      by_cases hjeq : j = degree H.nodes p + 1
      · subst hjeq; exact hpi
      · have hjle' : j ≤ degree H.nodes p := by omega
        have hdpos : 0 < degree H.nodes p := by omega
        have hdeg_mem : p ++ [degree H.nodes p] ∈ H.nodes := mem_degree_of_pos hdpos
        rw [expand_mem_iff]
        exact Or.inl (hord.2.2 p (degree H.nodes p) hdeg_mem j hj0 hjle')

lemma expand_label_sub_child {Q Sigma : Type} (B : SemNBW Q Sigma) {H : TreeData Q}
    (hv : Valid H) (σ : Sigma) {x : Node} {i : ℕ}
    (h : x ++ [i] ∈ (expand B H σ).nodes) :
    (expand B H σ).label (x ++ [i]) ⊆ (expand B H σ).label x := by
  rcases (expand_mem_iff B H σ (x ++ [i])).mp h with hH | ⟨z, hzH, heq⟩
  · have hxH : x ∈ H.nodes := hv.1.2.1 (x ++ [i]) hH x ⟨[i], rfl⟩
    rw [expand_label_old B H σ hH, expand_label_old B H σ hxH]
    have hsub : H.label (x ++ [i]) ⊆ H.label x := label_sub_of_prefix hv x [i] hH
    intro q hq
    obtain ⟨p, hp, hpq⟩ := Finset.mem_biUnion.mp hq
    exact Finset.mem_biUnion.mpr ⟨p, hsub hp, hpq⟩
  · obtain ⟨rfl, rfl⟩ := append_singleton_inj heq
    rw [expand_label_new B H σ hzH, expand_label_old B H σ hzH]
    exact Finset.inter_subset_left

lemma mem_horizontal_label_iff {Q : Type} (K : TreeData Q) (x : Node) (q : Q) :
    q ∈ (horizontal K).label x ↔
      q ∈ K.label x ∧ ¬ ∃ p i v j, x = p ++ i :: v ∧ 0 < j ∧ j < i ∧
        p ++ [j] ∈ K.nodes ∧ q ∈ K.label (p ++ [j]) := by
  simp [horizontal]

lemma horizontal_label_nil {Q : Type} (K : TreeData Q) :
    (horizontal K).label [] = K.label [] := by
  simp [horizontal]

lemma horizontal_disjoint {Q : Type} {K : TreeData Q} (hord : Ordered K.nodes)
    {p : Node} {i j : ℕ} (hi : p ++ [i] ∈ K.nodes) (hj : p ++ [j] ∈ K.nodes) (hne : i ≠ j) :
    Disjoint ((horizontal K).label (p ++ [i])) ((horizontal K).label (p ++ [j])) := by
  rw [Finset.disjoint_left]
  intro q hqi hqj
  simp only [horizontal, Finset.mem_filter] at hqi hqj
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hi0 : 0 < i := hord.1 (p ++ [i]) hi i (by simp)
    exact hqj.2 ⟨p, j, [], i, rfl, hi0, hlt, hi, hqi.1⟩
  · have hj0 : 0 < j := hord.1 (p ++ [j]) hj j (by simp)
    exact hqi.2 ⟨p, i, [], j, rfl, hj0, hgt, hj, hqj.1⟩

lemma horizontal_label_sub_child {Q : Type} {K : TreeData Q}
    (hsub : ∀ x i, x ++ [i] ∈ K.nodes → K.label (x ++ [i]) ⊆ K.label x)
    {x : Node} {i : ℕ} (h : x ++ [i] ∈ K.nodes) :
    (horizontal K).label (x ++ [i]) ⊆ (horizontal K).label x := by
  intro q hq
  simp only [horizontal, Finset.mem_filter] at hq ⊢
  refine ⟨hsub x i h hq.1, ?_⟩
  rintro ⟨p, k, v, j, rfl, hj0, hjk, hpj, hqpj⟩
  exact hq.2 ⟨p, k, v ++ [i], j, by simp, hj0, hjk, hpj, hqpj⟩

lemma horizontal_child_exists {Q : Type} {K : TreeData Q} (hord : Ordered K.nodes)
    {p : Node} {i : ℕ} {q : Q}
    (hpq : q ∈ (horizontal K).label p) (hpi : p ++ [i] ∈ K.nodes)
    (hq : q ∈ K.label (p ++ [i])) :
    ∃ j, 0 < j ∧ j ≤ i ∧ p ++ [j] ∈ K.nodes ∧ q ∈ (horizontal K).label (p ++ [j]) := by
  have hi0 : 0 < i := hord.1 (p ++ [i]) hpi i (by simp)
  let S := (Finset.Icc 1 i).filter (fun j => p ++ [j] ∈ K.nodes ∧ q ∈ K.label (p ++ [j]))
  have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hi0, le_rfl⟩, hpi, hq⟩
  let j0 := S.min' ⟨i, hiS⟩
  have hj0S : j0 ∈ S := Finset.min'_mem S ⟨i, hiS⟩
  simp only [S, Finset.mem_filter, Finset.mem_Icc] at hj0S
  obtain ⟨⟨hj01, hj0i⟩, hpj0, hqpj0⟩ := hj0S
  refine ⟨j0, hj01, hj0i, hpj0, ?_⟩
  simp only [horizontal, Finset.mem_filter]
  refine ⟨hqpj0, ?_⟩
  rintro ⟨p', k, v, j', heq, hj'0, hj'k, hp'j', hqp'j'⟩
  cases v using List.reverseRecOn with
  | nil =>
    have heq' : p ++ [j0] = p' ++ [k] := heq
    obtain ⟨rfl, rfl⟩ := append_singleton_inj heq'
    have hj'S : j' ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hj'0, by omega⟩, hp'j', hqp'j'⟩
    have hmin := Finset.min'_le S j' hj'S
    change j0 ≤ j' at hmin
    omega
  | append_singleton w last =>
    have heq' : p ++ [j0] = (p' ++ k :: w) ++ [last] := by simpa using heq
    obtain ⟨hp_eq, _⟩ := append_singleton_inj heq'
    simp only [horizontal, Finset.mem_filter] at hpq
    exact hpq.2 ⟨p', k, w, j', hp_eq, hj'0, hj'k, hp'j', hqp'j'⟩

lemma horizontal_dichotomy {Q : Type} {K : TreeData Q} (hord : Ordered K.nodes)
    (hsub : ∀ x i, x ++ [i] ∈ K.nodes → K.label (x ++ [i]) ⊆ K.label x) :
    ∀ x ∈ K.nodes, ∀ q ∈ K.label x,
      q ∈ (horizontal K).label x ∨
      ∃ p k v j, x = p ++ k :: v ∧ 0 < j ∧ j < k ∧
        p ++ [j] ∈ K.nodes ∧ q ∈ (horizontal K).label (p ++ [j]) := by
  intro x
  induction x using List.reverseRecOn with
  | nil =>
    intro _ q hq; left; rwa [horizontal_label_nil]
  | append_singleton y i ih =>
    intro hyi q hq
    have hy : y ∈ K.nodes := hord.2.1 (y ++ [i]) hyi y ⟨[i], rfl⟩
    have hqy : q ∈ K.label y := hsub y i hyi hq
    rcases ih hy q hqy with hqy_hor | ⟨p, k, v, j, rfl, hj0, hjk, hpj, hqpj⟩
    · obtain ⟨j, hj0, hjle, hyj, hqyj⟩ := horizontal_child_exists hord hqy_hor hyi hq
      by_cases hjeq : j = i
      · subst hjeq; exact Or.inl hqyj
      · exact Or.inr ⟨y, i, [], j, rfl, hj0, by omega, hyj, hqyj⟩
    · exact Or.inr ⟨p, k, v ++ [i], j, by simp, hj0, hjk, hpj, hqpj⟩

lemma stage3_mem_iff {Q Sigma : Type} (B : SemNBW Q Sigma) (H : TreeData Q) (σ : Sigma) (x : Node) :
    x ∈ (stage3 B H σ).nodes ↔
      x ∈ (expand B H σ).nodes ∧ ((horizontal (expand B H σ)).label x).Nonempty := by
  simp [stage3, removeEmpty, horizontal]

lemma stage3_label_of_mem {Q Sigma : Type} (B : SemNBW Q Sigma) (H : TreeData Q) (σ : Sigma)
    {x : Node} (hx : x ∈ (stage3 B H σ).nodes) :
    (stage3 B H σ).label x = (horizontal (expand B H σ)).label x := by
  change (if x ∈ (stage3 B H σ).nodes then (horizontal (expand B H σ)).label x else ∅) = _
  exact if_pos hx

lemma stage3_prefix_closed {Q Sigma : Type} (B : SemNBW Q Sigma) {H : TreeData Q}
    (hv : Valid H) (σ : Sigma) {x p : Node}
    (hx : x ∈ (stage3 B H σ).nodes) (hp : p.IsPrefix x) :
    p ∈ (stage3 B H σ).nodes := by
  have hord1 := expand_ordered B hv.1 σ
  have hsub1 := fun u i (h : u ++ [i] ∈ (expand B H σ).nodes) => expand_label_sub_child B hv σ h
  obtain ⟨w, rfl⟩ := hp
  induction w using List.reverseRecOn with
  | nil => simpa using hx
  | append_singleton u i ih =>
    have hx' : (p ++ u) ++ [i] ∈ (stage3 B H σ).nodes := by simpa using hx
    obtain ⟨hmem1, hne2⟩ := (stage3_mem_iff B H σ ((p ++ u) ++ [i])).mp hx'
    have hpu1 : p ++ u ∈ (expand B H σ).nodes := hord1.2.1 _ hmem1 (p ++ u) ⟨[i], rfl⟩
    have hsub2 := horizontal_label_sub_child hsub1 hmem1
    exact ih ((stage3_mem_iff B H σ (p ++ u)).mpr ⟨hpu1, hne2.mono hsub2⟩)

lemma stage3_childLabels_sub {Q Sigma : Type} (B : SemNBW Q Sigma) {H : TreeData Q}
    (hv : Valid H) (σ : Sigma) (x : Node) :
    childLabels (stage3 B H σ) x ⊆ (stage3 B H σ).label x := by
  intro q hq
  obtain ⟨y, hy_ch, hqy⟩ := Finset.mem_biUnion.mp hq
  simp only [children, Finset.mem_filter] at hy_ch
  obtain ⟨hy3, i, rfl⟩ := hy_ch
  have hx3 : x ∈ (stage3 B H σ).nodes := stage3_prefix_closed B hv σ hy3 ⟨[i], rfl⟩
  rw [stage3_label_of_mem B H σ hy3] at hqy
  rw [stage3_label_of_mem B H σ hx3]
  have hy1 : x ++ [i] ∈ (expand B H σ).nodes := ((stage3_mem_iff B H σ _).mp hy3).1
  exact horizontal_label_sub_child (fun u j h => expand_label_sub_child B hv σ h) hy1 hqy

lemma stage4_mem_iff {Q Sigma : Type} (B : SemNBW Q Sigma) (H : TreeData Q) (σ : Sigma) (x : Node) :
    x ∈ (stage4 B H σ).nodes ↔
      x ∈ (stage3 B H σ).nodes ∧ ¬ ∃ p ∈ resetNodes (stage3 B H σ), p.IsPrefix x ∧ p ≠ x := by
  simp [stage4, prune]

lemma stage4_prefix_closed {Q Sigma : Type} (B : SemNBW Q Sigma) {H : TreeData Q}
    (hv : Valid H) (σ : Sigma) {x q : Node}
    (hx : x ∈ (stage4 B H σ).nodes) (hq : q.IsPrefix x) :
    q ∈ (stage4 B H σ).nodes := by
  obtain ⟨hx3, hno⟩ := (stage4_mem_iff B H σ x).mp hx
  refine (stage4_mem_iff B H σ q).mpr ⟨stage3_prefix_closed B hv σ hx3 hq, ?_⟩
  rintro ⟨p, hp_res, hpq, hpne⟩
  apply hno
  refine ⟨p, hp_res, hpq.trans hq, ?_⟩
  intro hpx; subst hpx
  exact hpne (eq_of_prefix_of_length_eq hpq (le_antisymm hpq.length_le hq.length_le))

lemma stage4_positive {Q Sigma : Type} (B : SemNBW Q Sigma) {H : TreeData Q}
    (hv : Valid H) (σ : Sigma) {x : Node} (hx : x ∈ (stage4 B H σ).nodes) :
    Positive x := by
  have hx3 := ((stage4_mem_iff B H σ x).mp hx).1
  have hx1 := ((stage3_mem_iff B H σ x).mp hx3).1
  exact (expand_ordered B hv.1 σ).1 x hx1

lemma stage4_label_of_mem {Q Sigma : Type} (B : SemNBW Q Sigma) (H : TreeData Q) (σ : Sigma)
    {x : Node} (hx : x ∈ (stage4 B H σ).nodes) :
    (stage4 B H σ).label x = (stage3 B H σ).label x := by
  change (if x ∈ (stage4 B H σ).nodes then (stage3 B H σ).label x else ∅) = _
  exact if_pos hx

lemma stage4_children_of_reset {Q Sigma : Type} (B : SemNBW Q Sigma) (H : TreeData Q) (σ : Sigma)
    {x : Node} (hres : x ∈ resetNodes (stage3 B H σ)) :
    children (stage4 B H σ).nodes x = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro y hy
  simp only [children, Finset.mem_filter] at hy
  obtain ⟨hy4, i, rfl⟩ := hy
  obtain ⟨_, hno⟩ := (stage4_mem_iff B H σ (x ++ [i])).mp hy4
  exact hno ⟨x, hres, ⟨[i], rfl⟩, by simp⟩

lemma stage4_childLabels_ssubset {Q Sigma : Type} (B : SemNBW Q Sigma) {H : TreeData Q}
    (hv : Valid H) (σ : Sigma) {x : Node} (hx : x ∈ (stage4 B H σ).nodes) :
    childLabels (stage4 B H σ) x ⊂ (stage4 B H σ).label x := by
  obtain ⟨hx3, hno⟩ := (stage4_mem_iff B H σ x).mp hx
  rw [stage4_label_of_mem B H σ hx]
  by_cases hres : x ∈ resetNodes (stage3 B H σ)
  · have hch0 := stage4_children_of_reset B H σ hres
    have hcl0 : childLabels (stage4 B H σ) x = ∅ := by simp [childLabels, hch0]
    rw [hcl0, Finset.empty_ssubset, stage3_label_of_mem B H σ hx3]
    exact ((stage3_mem_iff B H σ x).mp hx3).2
  · have hch_eq : children (stage4 B H σ).nodes x = children (stage3 B H σ).nodes x := by
      ext y
      simp only [children, Finset.mem_filter]
      refine ⟨fun ⟨hy4, hi⟩ => ⟨((stage4_mem_iff B H σ y).mp hy4).1, hi⟩, ?_⟩
      rintro ⟨hy3, i, rfl⟩
      refine ⟨(stage4_mem_iff B H σ (x ++ [i])).mpr ⟨hy3, ?_⟩, i, rfl⟩
      rintro ⟨p, hpres, hpxi, hpne⟩
      have hpx : p.IsPrefix x := prefix_of_proper_prefix_concat hpxi hpne
      by_cases hpeqx : p = x
      · subst hpeqx; exact hres hpres
      · exact hno ⟨p, hpres, hpx, hpeqx⟩
    have hcl_eq : childLabels (stage4 B H σ) x = childLabels (stage3 B H σ) x := by
      unfold childLabels
      rw [hch_eq]
      refine Finset.biUnion_congr rfl fun y hy => ?_
      rw [← hch_eq] at hy
      exact stage4_label_of_mem B H σ (Finset.mem_filter.mp hy).1
    rw [hcl_eq]
    have hsub := stage3_childLabels_sub B hv σ x
    refine ssubset_of_subset_of_ne hsub fun heq => hres ?_
    exact Finset.mem_filter.mpr ⟨hx3, heq.symm⟩

lemma exists_stage4_anc {Q Sigma : Type} (B : SemNBW Q Sigma) {H : TreeData Q}
    (_hv : Valid H) (σ : Sigma) {u : Node} (hu : u ∈ (stage3 B H σ).nodes) :
    (u ∈ (stage4 B H σ).nodes) ∨
    (∃ v ∈ (stage4 B H σ).nodes, v ∈ resetNodes (stage3 B H σ) ∧ v.IsPrefix u ∧ v ≠ u) := by
  by_cases hu4 : u ∈ (stage4 B H σ).nodes
  · exact Or.inl hu4
  · right
    rw [stage4_mem_iff, not_and] at hu4
    have hex := hu4 hu
    rw [Classical.not_not] at hex
    let S := (Finset.range u.length).filter (fun k => u.take k ∈ resetNodes (stage3 B H σ))
    have hSne : S.Nonempty := by
      obtain ⟨p, hpres, hpu, hpne⟩ := hex
      have hplen : p.length < u.length :=
        lt_of_le_of_ne hpu.length_le (fun hl => hpne (eq_of_prefix_of_length_eq hpu hl))
      have htk : u.take p.length = p := by obtain ⟨t, rfl⟩ := hpu; exact List.take_left
      refine ⟨p.length, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hplen, ?_⟩⟩
      rwa [htk]
    let k0 := S.min' hSne
    have hk0S : k0 ∈ S := Finset.min'_mem S hSne
    simp only [S, Finset.mem_filter, Finset.mem_range] at hk0S
    obtain ⟨hk0_lt, hk0_res⟩ := hk0S
    let v := u.take k0
    have hvu : v.IsPrefix u := List.take_prefix k0 u
    have hvne : v ≠ u := by
      intro heq
      have hl := congrArg List.length heq
      rw [List.length_take_of_le (Nat.le_of_lt hk0_lt)] at hl
      omega
    have hv3 : v ∈ (stage3 B H σ).nodes := (Finset.mem_filter.mp hk0_res).1
    have hv4 : v ∈ (stage4 B H σ).nodes := by
      refine (stage4_mem_iff B H σ v).mpr ⟨hv3, ?_⟩
      rintro ⟨p, hpres, hpv, hpne⟩
      have hplen : p.length < k0 := by
        have hvlen : v.length = k0 := List.length_take_of_le (Nat.le_of_lt hk0_lt)
        have hle := hpv.length_le
        rw [hvlen] at hle
        exact lt_of_le_of_ne hle (fun hl => hpne (eq_of_prefix_of_length_eq hpv (hl.trans hvlen.symm)))
      have htk : u.take p.length = p := by
        obtain ⟨t, rfl⟩ := hpv.trans hvu; exact List.take_left
      have hpS : p.length ∈ S := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_trans hplen hk0_lt), ?_⟩
        rwa [htk]
      have hmin := Finset.min'_le S p.length hpS
      change k0 ≤ p.length at hmin
      omega
    exact ⟨v, hv4, hk0_res, hvu, hvne⟩

def childRank (T : Finset Node) (x : Node) (i : ℕ) : ℕ :=
  (T.filter fun y => ∃ j, y = x ++ [j] ∧ j < i).card + 1

lemma compress_nil (T : Finset Node) : compress T [] = [] := rfl

lemma getElem!_append_left {x y : List ℕ} {k : ℕ} (hk : k < x.length) :
    (x ++ y)[k]! = x[k]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]
  have hk' : k < (x ++ y).length := by simp; omega
  rw [List.getElem?_eq_getElem hk', List.getElem?_eq_getElem hk, List.getElem_append_left hk]

lemma getElem!_append_singleton_last (x : Node) (i : ℕ) :
    (x ++ [i])[x.length]! = i := by
  rw [List.getElem!_eq_getElem?_getD]
  have hk' : x.length < (x ++ [i]).length := by simp
  rw [List.getElem?_eq_getElem hk', List.getElem_append_right le_rfl]
  simp

lemma compress_concat (T : Finset Node) (x : Node) (i : ℕ) :
    compress T (x ++ [i]) = compress T x ++ [childRank T x i] := by
  unfold compress childRank
  simp only [List.length_append, List.length_singleton, List.range_succ, List.map_append,
    List.map_singleton]
  congr 1
  · refine List.map_congr_left fun k hk => ?_
    have hlt : k < x.length := List.mem_range.mp hk
    rw [List.take_append_of_le_length (Nat.le_of_lt hlt), getElem!_append_left hlt]
  · rw [List.take_left, getElem!_append_singleton_last]

lemma compress_length (T : Finset Node) (x : Node) :
    (compress T x).length = x.length := by
  simp [compress]

lemma compress_prefix (T : Finset Node) {p x : Node} (hp : p.IsPrefix x) :
    (compress T p).IsPrefix (compress T x) := by
  obtain ⟨w, rfl⟩ := hp
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton u i ih =>
    rw [← List.append_assoc, compress_concat]
    exact ih.trans ⟨[childRank T (p ++ u) i], rfl⟩

lemma childRank_eq_card_range (T : Finset Node) (x : Node) (i : ℕ) :
    childRank T x i = ((Finset.range i).filter (fun j => x ++ [j] ∈ T)).card + 1 := by
  unfold childRank
  congr 1
  have himg : (T.filter fun y => ∃ j, y = x ++ [j] ∧ j < i) =
      ((Finset.range i).filter (fun j => x ++ [j] ∈ T)).image (fun j => x ++ [j]) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hyT, j, rfl, hji⟩; exact ⟨j, ⟨hji, hyT⟩, rfl⟩
    · rintro ⟨j, ⟨hji, hjT⟩, rfl⟩; exact ⟨hjT, j, rfl, hji⟩
  rw [himg, Finset.card_image_of_injective]
  intro j1 j2 h
  exact (append_singleton_inj h).2

lemma childRank_strict_mono {T : Finset Node} {x : Node} {i1 i2 : ℕ}
    (h1 : x ++ [i1] ∈ T) (hlt : i1 < i2) :
    childRank T x i1 < childRank T x i2 := by
  rw [childRank_eq_card_range, childRank_eq_card_range]
  have hss : (Finset.range i1).filter (fun j => x ++ [j] ∈ T) ⊂
      (Finset.range i2).filter (fun j => x ++ [j] ∈ T) := by
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨i1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, h1⟩, by simp⟩
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact ⟨lt_trans hj.1 hlt, hj.2⟩
  have hc := Finset.card_lt_card hss
  omega

lemma childRank_le {T : Finset Node} (hpos : ∀ u ∈ T, Positive u)
    (x : Node) {i : ℕ} (hi : 0 < i) :
    childRank T x i ≤ i := by
  rw [childRank_eq_card_range]
  have hsub : (Finset.range i).filter (fun j => x ++ [j] ∈ T) ⊆ Finset.Icc 1 (i - 1) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hj ⊢
    have hj0 : 0 < j := hpos (x ++ [j]) hj.2 j (by simp)
    omega
  have hc := Finset.card_le_card hsub
  simp only [Nat.card_Icc] at hc
  omega

lemma childRank_surj {T : Finset Node} {x : Node} :
    ∀ (i : ℕ), x ++ [i] ∈ T → ∀ s, 0 < s → s ≤ childRank T x i →
      ∃ j ≤ i, x ++ [j] ∈ T ∧ childRank T x j = s := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hiT s hs0 hsle
    by_cases hseq : s = childRank T x i
    · exact ⟨i, le_rfl, hiT, hseq.symm⟩
    · have hslt : s < childRank T x i := lt_of_le_of_ne hsle hseq
      rw [childRank_eq_card_range] at hslt
      let A := (Finset.range i).filter (fun j => x ++ [j] ∈ T)
      have hA_card_gt : s < A.card + 1 := hslt
      have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
      let i' := A.max' hAne
      have hi'A : i' ∈ A := Finset.max'_mem A hAne
      simp only [A, Finset.mem_filter, Finset.mem_range] at hi'A
      obtain ⟨hi'lt, hi'T⟩ := hi'A
      have hAeq : A = insert i' ((Finset.range i').filter (fun j => x ++ [j] ∈ T)) := by
        ext j
        simp only [A, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
        constructor
        · rintro ⟨hji, hjT⟩
          have hjle : j ≤ i' := Finset.le_max' A j
            (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hji, hjT⟩)
          by_cases hjeq : j = i'
          · exact Or.inl hjeq
          · exact Or.inr ⟨by omega, hjT⟩
        · rintro (rfl | ⟨hji', hjT⟩)
          · exact ⟨hi'lt, hi'T⟩
          · exact ⟨lt_trans hji' hi'lt, hjT⟩
      have hcardA : A.card = ((Finset.range i').filter (fun j => x ++ [j] ∈ T)).card + 1 := by
        rw [hAeq, Finset.card_insert_of_notMem (by simp)]
      have hsle' : s ≤ childRank T x i' := by
        rw [childRank_eq_card_range]; omega
      obtain ⟨j, hjle', hjT, hjr⟩ := ih i' hi'lt hi'T s hs0 hsle'
      exact ⟨j, le_trans hjle' (Nat.le_of_lt hi'lt), hjT, hjr⟩

lemma compress_inj_on {T : Finset Node}
    (hpref : ∀ u ∈ T, ∀ p, p.IsPrefix u → p ∈ T) :
    ∀ x ∈ T, ∀ y ∈ T, compress T x = compress T y → x = y := by
  intro x
  induction x using List.reverseRecOn with
  | nil =>
    intro _ y _ heq
    have hl := congrArg List.length heq
    rw [compress_nil, compress_length] at hl
    exact (List.eq_nil_of_length_eq_zero hl.symm).symm
  | append_singleton x' i ih =>
    intro hx y hy heq
    cases y using List.reverseRecOn with
    | nil =>
      have hl := congrArg List.length heq
      rw [compress_nil, compress_length] at hl
      simp at hl
    | append_singleton y' j =>
      rw [compress_concat, compress_concat] at heq
      obtain ⟨heq_pre, heq_rk⟩ := append_singleton_inj heq
      have hx' : x' ∈ T := hpref (x' ++ [i]) hx x' ⟨[i], rfl⟩
      have hy' : y' ∈ T := hpref (y' ++ [j]) hy y' ⟨[j], rfl⟩
      have hxy' : x' = y' := ih hx' y' hy' heq_pre
      subst hxy'
      rcases lt_trichotomy i j with hlt | rfl | hgt
      · exfalso; have := childRank_strict_mono hx hlt; omega
      · rfl
      · exfalso; have := childRank_strict_mono hy hgt; omega

lemma compressed_label_of_mem {Q : Type} {K : TreeData Q}
    (hpref : ∀ u ∈ K.nodes, ∀ p, p.IsPrefix u → p ∈ K.nodes)
    {x : Node} (hx : x ∈ K.nodes) :
    (compressed K).label (compress K.nodes x) = K.label x := by
  unfold compressed
  simp only
  have hflt : (K.nodes.filter fun y => compress K.nodes y = compress K.nodes x) = {x} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun ⟨hy, heq⟩ => compress_inj_on hpref y hy x hx heq, fun hyx => ⟨hyx ▸ hx, hyx ▸ rfl⟩⟩
  rw [hflt, Finset.singleton_biUnion]

lemma compressed_children_of_mem {Q : Type} {K : TreeData Q}
    (hpref : ∀ u ∈ K.nodes, ∀ p, p.IsPrefix u → p ∈ K.nodes)
    {x : Node} (hx : x ∈ K.nodes) :
    children (compressed K).nodes (compress K.nodes x) =
      (children K.nodes x).image (compress K.nodes) := by
  ext z
  simp only [compressed, children, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨y, hyK, rfl⟩, r, heq⟩
    cases y using List.reverseRecOn with
    | nil => rw [compress_nil] at heq; simp at heq
    | append_singleton x' i =>
      rw [compress_concat] at heq
      obtain ⟨heq_pre, _⟩ := append_singleton_inj heq
      have hx'K : x' ∈ K.nodes := hpref (x' ++ [i]) hyK x' ⟨[i], rfl⟩
      have hx'eq : x' = x := compress_inj_on hpref x' hx'K x hx heq_pre
      rw [hx'eq] at hyK ⊢
      exact ⟨x ++ [i], ⟨hyK, i, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨hyK, i, rfl⟩, rfl⟩
    exact ⟨⟨x ++ [i], hyK, rfl⟩, childRank K.nodes x i, compress_concat K.nodes x i⟩

lemma compressed_valid {Q : Type} {K : TreeData Q}
    (_hpos : ∀ u ∈ K.nodes, Positive u)
    (hpref : ∀ u ∈ K.nodes, ∀ p, p.IsPrefix u → p ∈ K.nodes)
    (hroot : [] ∈ K.nodes)
    (hne : ∀ u ∈ K.nodes, (K.label u).Nonempty)
    (hdisj : ∀ p i j, p ++ [i] ∈ K.nodes → p ++ [j] ∈ K.nodes → i ≠ j →
      Disjoint (K.label (p ++ [i])) (K.label (p ++ [j])))
    (hssub : ∀ u ∈ K.nodes, childLabels K u ⊂ K.label u) :
    Valid (compressed K) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    intro r hr
    unfold compress at hr
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hr
    omega
  · intro z hz p hp
    obtain ⟨x, hxK, rfl⟩ := Finset.mem_image.mp hz
    have hlen : p.length ≤ x.length := by simpa [compress_length] using hp.length_le
    have htk_pre : (x.take p.length).IsPrefix x := List.take_prefix p.length x
    have htkK : x.take p.length ∈ K.nodes := hpref x hxK _ htk_pre
    have hcp_pre : (compress K.nodes (x.take p.length)).IsPrefix (compress K.nodes x) :=
      compress_prefix K.nodes htk_pre
    have hcp_len : (compress K.nodes (x.take p.length)).length = p.length := by
      rw [compress_length, List.length_take_of_le hlen]
    have hp_eq : p = compress K.nodes (x.take p.length) := by
      obtain ⟨t1, ht1⟩ := hp
      obtain ⟨t2, ht2⟩ := hcp_pre
      have := congrArg (List.take p.length) (ht1.trans ht2.symm)
      rw [List.take_left, List.take_left' hcp_len] at this
      exact this
    rw [hp_eq]
    exact Finset.mem_image.mpr ⟨x.take p.length, htkK, rfl⟩
  · intro p' r hp'r s hs0 hsle
    obtain ⟨y, hyK, heq⟩ := Finset.mem_image.mp hp'r
    cases y using List.reverseRecOn with
    | nil => rw [compress_nil] at heq; simp at heq
    | append_singleton x i =>
      rw [compress_concat] at heq
      obtain ⟨rfl, rfl⟩ := append_singleton_inj heq
      obtain ⟨j, _, hjK, hjrk⟩ := childRank_surj i hyK s hs0 hsle
      refine Finset.mem_image.mpr ⟨x ++ [j], hjK, ?_⟩
      rw [compress_concat, hjrk]
  · exact Finset.mem_image.mpr ⟨[], hroot, rfl⟩
  · intro z hz
    simp only [compressed, Finset.mem_image, not_exists, not_and] at hz ⊢
    ext q
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.notMem_empty, iff_false]
    rintro ⟨y, ⟨hy1, hy2⟩, _⟩
    exact hz y hy1 hy2
  · intro z hz
    obtain ⟨x, hxK, rfl⟩ := Finset.mem_image.mp hz
    rw [compressed_label_of_mem hpref hxK]
    exact hne x hxK
  · intro p' r1 r2 h1 h2 hrne
    obtain ⟨y1, hy1K, heq1⟩ := Finset.mem_image.mp h1
    obtain ⟨y2, hy2K, heq2⟩ := Finset.mem_image.mp h2
    cases y1 using List.reverseRecOn with
    | nil => rw [compress_nil] at heq1; simp at heq1
    | append_singleton x1 i1 =>
      cases y2 using List.reverseRecOn with
      | nil => rw [compress_nil] at heq2; simp at heq2
      | append_singleton x2 i2 =>
        have h1' := heq1; rw [compress_concat] at h1'
        have h2' := heq2; rw [compress_concat] at h2'
        obtain ⟨hx1p, hr1⟩ := append_singleton_inj h1'
        obtain ⟨hx2p, hr2⟩ := append_singleton_inj h2'
        have hx1K : x1 ∈ K.nodes := hpref _ hy1K x1 ⟨[i1], rfl⟩
        have hx2K : x2 ∈ K.nodes := hpref _ hy2K x2 ⟨[i2], rfl⟩
        have hx12 : x1 = x2 := compress_inj_on hpref x1 hx1K x2 hx2K (hx1p.trans hx2p.symm)
        subst hx12
        have hine : i1 ≠ i2 := fun hieq => hrne (hr1 ▸ hr2 ▸ hieq ▸ rfl)
        rw [← heq1, ← heq2, compressed_label_of_mem hpref hy1K, compressed_label_of_mem hpref hy2K]
        exact hdisj x1 i1 i2 hy1K hy2K hine
  · intro z hz
    obtain ⟨x, hxK, rfl⟩ := Finset.mem_image.mp hz
    have hcl : childLabels (compressed K) (compress K.nodes x) = childLabels K x := by
      unfold childLabels
      rw [compressed_children_of_mem hpref hxK]
      ext q
      simp only [Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, hq⟩
        rw [compressed_label_of_mem hpref (Finset.mem_filter.mp hy).1] at hq
        exact ⟨y, hy, hq⟩
      · rintro ⟨y, hy, hq⟩
        refine ⟨compress K.nodes y, ⟨y, hy, rfl⟩, ?_⟩
        rwa [compressed_label_of_mem hpref (Finset.mem_filter.mp hy).1]
    rw [hcl, compressed_label_of_mem hpref hxK]
    exact hssub x hxK

lemma stage4_valid_compressed {Q Sigma : Type} (B : SemNBW Q Sigma)
    (H : History Q) (σ : Sigma) (hroot : [] ∈ (stage4 B H.val σ).nodes) :
    Valid (compressed (stage4 B H.val σ)) := by
  have hv := H.property
  refine compressed_valid
    (fun u hu => stage4_positive B hv σ hu)
    (fun u hu p hp => stage4_prefix_closed B hv σ hu hp)
    hroot
    (fun u hu => by
      rw [stage4_label_of_mem B H.val σ hu]
      have hu3 := ((stage4_mem_iff B H.val σ u).mp hu).1
      rw [stage3_label_of_mem B H.val σ hu3]
      exact ((stage3_mem_iff B H.val σ u).mp hu3).2)
    (fun p i j hi4 hj4 hne => by
      rw [stage4_label_of_mem B H.val σ hi4, stage4_label_of_mem B H.val σ hj4]
      have hi3 := ((stage4_mem_iff B H.val σ _).mp hi4).1
      have hj3 := ((stage4_mem_iff B H.val σ _).mp hj4).1
      rw [stage3_label_of_mem B H.val σ hi3, stage3_label_of_mem B H.val σ hj3]
      have hi1 := ((stage3_mem_iff B H.val σ _).mp hi3).1
      have hj1 := ((stage3_mem_iff B H.val σ _).mp hj3).1
      exact horizontal_disjoint (expand_ordered B hv.1 σ) hi1 hj1 hne)
    (fun u hu => stage4_childLabels_ssubset B hv σ hu)

lemma root_mem_stage4_iff {Q Sigma : Type} (B : SemNBW Q Sigma) (H : History Q) (σ : Sigma) :
    [] ∈ (stage4 B H.val σ).nodes ↔
      ((H.val.label []).biUnion (fun q => B.delta q σ)).Nonempty := by
  rw [stage4_mem_iff]
  have hno : ¬ ∃ p ∈ resetNodes (stage3 B H.val σ), p.IsPrefix [] ∧ p ≠ [] := by
    rintro ⟨p, _, hp, hne⟩; exact hne (List.prefix_nil.mp hp)
  simp only [hno, not_false_eq_true, and_true, stage3_mem_iff, horizontal_label_nil]
  have hroot1 : [] ∈ (expand B H.val σ).nodes := by
    rw [expand_mem_iff]; exact Or.inl H.property.2.1
  simp [hroot1, expand_label_old B H.val σ H.property.2.1]

lemma successor_eq_some_iff {Q Sigma : Type} (B : SemNBW Q Sigma)
    (H : History Q) (σ : Sigma) (H' : History Q) :
    successor B H σ = some H' ↔ H'.val = compressed (stage4 B H.val σ) := by
  unfold successor asHistory
  split_ifs with hv
  · simp [Subtype.ext_iff, eq_comm]
  · constructor
    · intro h; cases h
    · intro heq; exact absurd (heq ▸ H'.property) hv

lemma root_mem_stage4_of_succ {Q Sigma : Type} (B : SemNBW Q Sigma)
    {H H' : History Q} {σ : Sigma} (hsucc : successor B H σ = some H') :
    [] ∈ (stage4 B H.val σ).nodes := by
  have heq := (successor_eq_some_iff B H σ H').mp hsucc
  have hroot_c : [] ∈ (compressed (stage4 B H.val σ)).nodes := heq ▸ H'.property.2.1
  obtain ⟨y, hy4, hyc⟩ := Finset.mem_image.mp hroot_c
  have hy0 : y = [] := by
    have hl := congrArg List.length hyc
    rw [compress_length] at hl
    exact List.eq_nil_of_length_eq_zero hl
  rwa [← hy0]

lemma succ_label_root {Q Sigma : Type} (B : SemNBW Q Sigma)
    {H H' : History Q} {σ : Sigma} (hsucc : successor B H σ = some H') :
    H'.val.label [] = (H.val.label []).biUnion (fun q => B.delta q σ) := by
  have heq := (successor_eq_some_iff B H σ H').mp hsucc
  have hroot4 : [] ∈ (stage4 B H.val σ).nodes := root_mem_stage4_of_succ B hsucc
  have hroot3 : [] ∈ (stage3 B H.val σ).nodes := ((stage4_mem_iff B H.val σ []).mp hroot4).1
  rw [heq]
  have hc := compressed_label_of_mem
    (fun u hu p hp => stage4_prefix_closed B H.property σ hu hp) hroot4
  rw [compress_nil] at hc
  rw [hc, stage4_label_of_mem B H.val σ hroot4, stage3_label_of_mem B H.val σ hroot3,
    horizontal_label_nil, expand_label_old B H.val σ H.property.2.1]

lemma valid_initialData_iff {Q Sigma : Type} (B : SemNBW Q Sigma) :
    Valid (initialData B) ↔ B.initial.Nonempty := by
  constructor
  · intro hv
    simpa [initialData] using hv.2.2.2.1 [] (by simp [initialData])
  · intro hne
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx; simp [initialData] at hx; subst hx; intro i hi; simp at hi
    · intro x hx p hp
      simp [initialData] at hx; subst hx
      rcases List.prefix_nil.mp hp with rfl
      simp [initialData]
    · intro p i hpi; simp [initialData] at hpi
    · simp [initialData]
    · intro x hx; simp [initialData] at hx; simp [initialData, hx]
    · intro x hx; simp [initialData] at hx; subst hx; simpa [initialData] using hne
    · intro p i _ hpi; simp [initialData] at hpi
    · intro x hx
      simp [initialData] at hx; subst hx
      have hch : children (initialData B).nodes [] = ∅ := by
        ext y
        simp only [children, initialData, Finset.mem_filter, Finset.mem_singleton,
          Finset.notMem_empty, iff_false]
        rintro ⟨rfl, i, h⟩; simp at h
      have hcl : childLabels (initialData B) [] = ∅ := by simp [childLabels, hch]
      rw [hcl, Finset.empty_ssubset]
      simpa [initialData] using hne

lemma initialHistory_of_nonempty {Q Sigma : Type} (B : SemNBW Q Sigma) (hne : B.initial.Nonempty) :
    ∃ H0 : History Q, initialHistory B = some H0 ∧ H0.val = initialData B := by
  have hv := (valid_initialData_iff B).mpr hne
  exact ⟨⟨initialData B, hv⟩, dif_pos hv, rfl⟩

lemma noninc_stabilizes (f : ℕ → ℕ) (h : ∀ k, f (k + 1) ≤ f k) :
    ∃ K, ∀ k ≥ K, f k = f K := by
  have hle_zero : ∀ (g : ℕ → ℕ), (∀ k, g (k + 1) ≤ g k) → ∀ t, g t ≤ g 0 := by
    intro g hg t
    induction t with
    | zero => exact le_rfl
    | succ t iht => exact le_trans (hg t) iht
  suffices ∀ m : ℕ, ∀ g : ℕ → ℕ, (∀ k, g (k + 1) ≤ g k) → g 0 ≤ m → ∃ K, ∀ k ≥ K, g k = g K from
    this (f 0) f h le_rfl
  intro m
  induction m with
  | zero =>
    intro g hg hg0
    refine ⟨0, fun k _ => ?_⟩
    have := hle_zero g hg k; omega
  | succ m ih =>
    intro g hg hg0
    by_cases hall : ∀ k, g k = g 0
    · exact ⟨0, fun k _ => hall k⟩
    · obtain ⟨k0, hk0⟩ := Classical.not_forall.mp hall
      have hk0_lt : g k0 < g 0 := lt_of_le_of_ne (hle_zero g hg k0) hk0
      let g' : ℕ → ℕ := fun t => g (k0 + t)
      have hg'0 : g' 0 ≤ m := by change g (k0 + 0) ≤ m; rw [Nat.add_zero]; omega
      obtain ⟨K', hK'⟩ := ih g' (fun t => by simpa [g', Nat.add_assoc] using hg (k0 + t)) hg'0
      refine ⟨k0 + K', fun k hk => ?_⟩
      have heq := hK' (k - k0) (by omega)
      simpa [g', show k0 + (k - k0) = k by omega] using heq

lemma step_owner_transition {Q Sigma : Type} [Fintype Q]
    (B : SemNBW Q Sigma) {H H' : History Q} {σ : Sigma}
    (hsucc : successor B H σ = some H')
    {q q' : Q} (hdelta : q' ∈ B.delta q σ)
    {x x' : Node} (hx : x ∈ H.val.nodes) (hown : q ∈ own H.val x)
    (hx' : x' ∈ H'.val.nodes) (hown' : q' ∈ own H'.val x')
    {p : Node} (hp_pre : p.IsPrefix x) (hp_pre' : p.IsPrefix x')
    (hp4 : p ∈ (stage4 B H.val σ).nodes)
    (hp_comp : compress (stage4 B H.val σ).nodes p = p)
    (hp_nores : p ∉ resetNodes (stage3 B H.val σ)) :
    (x = p → q' ∈ B.accepting → p.length < x'.length) ∧
    (∀ c rest, x = p ++ c :: rest →
      ∃ j c', 0 < j ∧ j ≤ c ∧ p ++ [j] ∈ (stage4 B H.val σ).nodes ∧
        c' = childRank (stage4 B H.val σ).nodes p j ∧ c' ≤ j ∧
        (p ++ [c']).IsPrefix x') := by
  have hv := H.property
  have hv' := H'.property
  have hH'_eq : H'.val = compressed (stage4 B H.val σ) :=
    (successor_eq_some_iff B H σ H').mp hsucc
  let H1 := expand B H.val σ
  let H3 := stage3 B H.val σ
  let H4 := stage4 B H.val σ
  have hord1 := expand_ordered B hv.1 σ
  have hsub1 := fun u i (h : u ++ [i] ∈ H1.nodes) => expand_label_sub_child B hv σ h
  have hpref4 : ∀ u ∈ H4.nodes, ∀ r, r.IsPrefix u → r ∈ H4.nodes :=
    fun u hu r hr => stage4_prefix_closed B hv σ hu hr
  have hpos4 : ∀ u ∈ H4.nodes, Positive u := fun u hu => stage4_positive B hv σ hu
  have hqx : q ∈ H.val.label x := (Finset.mem_sdiff.mp hown).1
  have hq'1_x : q' ∈ H1.label x := by
    rw [expand_label_old B H.val σ hx]
    exact Finset.mem_biUnion.mpr ⟨q, hqx, hdelta⟩
  have no_jump_before_p : ∀ (p0 : Node) (k j : ℕ) (v : List ℕ),
      p0.length < p.length → p.IsPrefix (p0 ++ k :: v) →
      0 < j → j < k → p0 ++ [j] ∈ H1.nodes →
      q' ∈ (horizontal H1).label (p0 ++ [j]) → False := by
    intro p0 k j v hp0len hp_p0 hj0 hjk hp0j hq'p0j
    have hp0j_3 : p0 ++ [j] ∈ H3.nodes :=
      (stage3_mem_iff B H.val σ _).mpr ⟨hp0j, ⟨q', hq'p0j⟩⟩
    have hp0k_pre_p : (p0 ++ [k]).IsPrefix p := by
      obtain ⟨t, ht⟩ := hp_p0
      have htk := congrArg (List.take (p0.length + 1)) ht
      have h1 : (p ++ t).take (p0.length + 1) = p.take (p0.length + 1) :=
        List.take_append_of_le_length (by omega)
      have h2 : (p0 ++ k :: v).take (p0.length + 1) = p0 ++ [k] := by
        have : p0 ++ k :: v = (p0 ++ [k]) ++ v := by simp
        rw [this, List.take_left' (by simp)]
      rw [h1, h2] at htk; rw [← htk]; exact List.take_prefix _ _
    have hp0_pre_p : p0.IsPrefix p := List.IsPrefix.trans ⟨[k], rfl⟩ hp0k_pre_p
    rcases exists_stage4_anc B hv σ hp0j_3 with hp0j_4 | ⟨v0, _, hv0_res, hv0_pre, hv0_ne⟩
    · have hp0_comp : compress H4.nodes p0 = p0 := by
        have hcp := compress_prefix H4.nodes hp0_pre_p
        rw [hp_comp] at hcp
        obtain ⟨t1, ht1⟩ := hcp; obtain ⟨t2, ht2⟩ := hp0_pre_p
        have htk := congrArg (List.take p0.length) (ht1.trans ht2.symm)
        rw [List.take_left' (compress_length H4.nodes p0), List.take_left] at htk
        exact htk
      let z' := compress H4.nodes (p0 ++ [j])
      have hz'_eq : z' = p0 ++ [childRank H4.nodes p0 j] := by
        simp [z', compress_concat, hp0_comp]
      have hz'_mem : z' ∈ H'.val.nodes := by
        rw [hH'_eq]; exact Finset.mem_image.mpr ⟨p0 ++ [j], hp0j_4, rfl⟩
      have hq'z' : q' ∈ H'.val.label z' := by
        rw [hH'_eq, compressed_label_of_mem hpref4 hp0j_4,
          stage4_label_of_mem B H.val σ hp0j_4, stage3_label_of_mem B H.val σ hp0j_3]
        exact hq'p0j
      have hz'_pre_x' : z'.IsPrefix x' :=
        (mem_label_iff_prefix_own hv' hx' hown' hz'_mem).mp hq'z'
      have hp0k_pre_x' : (p0 ++ [k]).IsPrefix x' := hp0k_pre_p.trans hp_pre'
      rw [hz'_eq] at hz'_pre_x'
      obtain ⟨t1, ht1⟩ := hz'_pre_x'; obtain ⟨t2, ht2⟩ := hp0k_pre_x'
      have htk := congrArg (List.take (p0.length + 1)) (ht1.trans ht2.symm)
      have hl1 : ((p0 ++ [childRank H4.nodes p0 j]) ++ t1).take (p0.length + 1) =
          p0 ++ [childRank H4.nodes p0 j] := List.take_left' (by simp)
      have hl2 : ((p0 ++ [k]) ++ t2).take (p0.length + 1) = p0 ++ [k] := List.take_left' (by simp)
      rw [hl1, hl2] at htk
      have hrk_eq : childRank H4.nodes p0 j = k := (append_singleton_inj htk).2
      have hrk_le : childRank H4.nodes p0 j ≤ j := childRank_le hpos4 p0 hj0
      omega
    · have hv0_pre_p0 : v0.IsPrefix p0 := prefix_of_proper_prefix_concat hv0_pre hv0_ne
      have hv0_pre_p : v0.IsPrefix p := hv0_pre_p0.trans hp0_pre_p
      have hv0_ne_p : v0 ≠ p := by intro heq; subst heq; have := hv0_pre_p0.length_le; omega
      obtain ⟨_, hno4⟩ := (stage4_mem_iff B H.val σ p).mp hp4
      exact hno4 ⟨v0, hv0_res, hv0_pre_p, hv0_ne_p⟩
  have push_child : ∀ {u : Node} {j : ℕ},
      0 < j → (p ++ [j]).IsPrefix u → u ∈ H3.nodes → q' ∈ H3.label u →
      p ++ [j] ∈ H4.nodes ∧ (p ++ [childRank H4.nodes p j]).IsPrefix x' := by
    intro u j hj0 hpju hu3 hq'u3
    have hpj3 : p ++ [j] ∈ H3.nodes := stage3_prefix_closed B hv σ hu3 hpju
    have hpj4 : p ++ [j] ∈ H4.nodes := by
      refine (stage4_mem_iff B H.val σ (p ++ [j])).mpr ⟨hpj3, ?_⟩
      rintro ⟨r, hr_res, hr_pre, hr_ne⟩
      have hr_pre_p : r.IsPrefix p := prefix_of_proper_prefix_concat hr_pre hr_ne
      by_cases hreq : r = p
      · subst hreq; exact hp_nores hr_res
      · exact ((stage4_mem_iff B H.val σ p).mp hp4).2 ⟨r, hr_res, hr_pre_p, hreq⟩
    rcases exists_stage4_anc B hv σ hu3 with hu4 | ⟨v0, hv0_4, hv0_res, hv0_pre, _⟩
    · let z' := compress H4.nodes u
      have hz'mem : z' ∈ H'.val.nodes := by rw [hH'_eq]; exact Finset.mem_image.mpr ⟨u, hu4, rfl⟩
      have hq'z' : q' ∈ H'.val.label z' := by
        rw [hH'_eq, compressed_label_of_mem hpref4 hu4, stage4_label_of_mem B H.val σ hu4]
        exact hq'u3
      have hz'_pre : z'.IsPrefix x' := (mem_label_iff_prefix_own hv' hx' hown' hz'mem).mp hq'z'
      have hcp_pj : (compress H4.nodes (p ++ [j])).IsPrefix z' := compress_prefix H4.nodes hpju
      rw [compress_concat, hp_comp] at hcp_pj
      exact ⟨hpj4, hcp_pj.trans hz'_pre⟩
    · have hpj_pre_v0 : (p ++ [j]).IsPrefix v0 := by
        by_cases hlen : v0.length ≤ p.length
        · exfalso
          obtain ⟨t1, ht1⟩ := hv0_pre; obtain ⟨t2, ht2⟩ := hpju
          have htk := congrArg (List.take v0.length) (ht1.trans ht2.symm)
          rw [List.take_left] at htk
          have hrhs : ((p ++ [j]) ++ t2).take v0.length = p.take v0.length := by
            rw [List.append_assoc, List.take_append_of_le_length hlen]
          rw [hrhs] at htk
          have hv0_pre_p : v0.IsPrefix p := htk ▸ List.take_prefix v0.length p
          by_cases hv0eq : v0 = p
          · subst hv0eq; exact hp_nores hv0_res
          · exact ((stage4_mem_iff B H.val σ p).mp hp4).2 ⟨v0, hv0_res, hv0_pre_p, hv0eq⟩
        · have hge : (p ++ [j]).length ≤ v0.length := by simp; omega
          obtain ⟨t1, ht1⟩ := hpju; obtain ⟨t2, ht2⟩ := hv0_pre
          have htk := congrArg (List.take (p ++ [j]).length) (ht1.trans ht2.symm)
          rw [List.take_left, List.take_append_of_le_length hge] at htk
          exact htk ▸ List.take_prefix _ _
      have hq'v0_3 : q' ∈ H3.label v0 := by
        obtain ⟨t, rfl⟩ := hv0_pre
        have hsub : ∀ (a : Node) (b : List ℕ), a ++ b ∈ H3.nodes →
            H3.label (a ++ b) ⊆ H3.label a := by
          intro a b
          induction b using List.reverseRecOn with
          | nil => intro _; simp
          | append_singleton b' last ih =>
            intro hab
            have hab' : (a ++ b') ++ [last] ∈ H3.nodes := by simpa using hab
            have hab1 : a ++ b' ∈ H3.nodes := stage3_prefix_closed B hv σ hab' ⟨[last], rfl⟩
            have hs1 : H3.label ((a ++ b') ++ [last]) ⊆ childLabels H3 (a ++ b') :=
              Finset.subset_biUnion_of_mem H3.label (Finset.mem_filter.mpr ⟨hab', last, rfl⟩)
            have hs2 := stage3_childLabels_sub B hv σ (a ++ b')
            have hs3 : H3.label (a ++ (b' ++ [last])) ⊆ H3.label (a ++ b') := by
              simpa using hs1.trans hs2
            exact hs3.trans (ih hab1)
        exact hsub v0 t hu3 hq'u3
      let z' := compress H4.nodes v0
      have hz'mem : z' ∈ H'.val.nodes := by rw [hH'_eq]; exact Finset.mem_image.mpr ⟨v0, hv0_4, rfl⟩
      have hq'z' : q' ∈ H'.val.label z' := by
        rw [hH'_eq, compressed_label_of_mem hpref4 hv0_4, stage4_label_of_mem B H.val σ hv0_4]
        exact hq'v0_3
      have hz'_pre : z'.IsPrefix x' := (mem_label_iff_prefix_own hv' hx' hown' hz'mem).mp hq'z'
      have hcp_pj : (compress H4.nodes (p ++ [j])).IsPrefix z' := compress_prefix H4.nodes hpj_pre_v0
      rw [compress_concat, hp_comp] at hcp_pj
      exact ⟨hpj4, hcp_pj.trans hz'_pre⟩
  refine ⟨?_, ?_⟩
  · intro hxp hq'acc
    subst hxp
    let d := degree H.val.nodes x
    let w := x ++ [d + 1]
    have hw1 : w ∈ H1.nodes := by rw [expand_mem_iff]; exact Or.inr ⟨x, hx, rfl⟩
    have hq'w1 : q' ∈ H1.label w := by
      rw [expand_label_new B H.val σ hx]
      exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨q, hqx, hdelta⟩, hq'acc⟩
    rcases horizontal_dichotomy hord1 hsub1 w hw1 q' hq'w1 with
      hq'w2 | ⟨p0, k, v, j, heq, hj0, hjk, hp0j, hq'p0j⟩
    · have hw3 : w ∈ H3.nodes := (stage3_mem_iff B H.val σ w).mpr ⟨hw1, ⟨q', hq'w2⟩⟩
      have hq'w3 : q' ∈ H3.label w := by rwa [stage3_label_of_mem B H.val σ hw3]
      obtain ⟨_, hpre'⟩ := push_child (Nat.succ_pos d) (List.prefix_refl w) hw3 hq'w3
      have hlen := hpre'.length_le; simp at hlen; omega
    · by_cases hp0len : p0.length < x.length
      · exact False.elim (no_jump_before_p p0 k j v hp0len (heq ▸ ⟨[d + 1], rfl⟩) hj0 hjk hp0j hq'p0j)
      · have hv_nil : v = [] := by
          have hl := congrArg List.length heq; simp [w] at hl
          exact List.eq_nil_of_length_eq_zero (by omega)
        subst hv_nil
        obtain ⟨rfl, rfl⟩ := append_singleton_inj heq
        have hp0j_3 : x ++ [j] ∈ H3.nodes := (stage3_mem_iff B H.val σ _).mpr ⟨hp0j, ⟨q', hq'p0j⟩⟩
        have hq'p0j_3 : q' ∈ H3.label (x ++ [j]) := by rwa [stage3_label_of_mem B H.val σ hp0j_3]
        obtain ⟨_, hpre'⟩ := push_child hj0 (List.prefix_refl _) hp0j_3 hq'p0j_3
        have hlen := hpre'.length_le; simp at hlen; omega
  · intro c rest hxeq
    have hc0 : 0 < c := hv.1.1 x hx c (by simp [hxeq])
    have hx1 : x ∈ H1.nodes := (expand_mem_iff B H.val σ x).mpr (Or.inl hx)
    rcases horizontal_dichotomy hord1 hsub1 x hx1 q' hq'1_x with
      hq'x2 | ⟨p0, k, v, j, heq, hj0, hjk, hp0j, hq'p0j⟩
    · have hx3 : x ∈ H3.nodes := (stage3_mem_iff B H.val σ x).mpr ⟨hx1, ⟨q', hq'x2⟩⟩
      have hq'x3 : q' ∈ H3.label x := by rwa [stage3_label_of_mem B H.val σ hx3]
      have hp_c_pre : (p ++ [c]).IsPrefix x := by rw [hxeq]; exact ⟨rest, by simp⟩
      obtain ⟨hpc4, hpre'⟩ := push_child hc0 hp_c_pre hx3 hq'x3
      exact ⟨c, childRank H4.nodes p c, hc0, le_rfl, hpc4, rfl, childRank_le hpos4 p hc0, hpre'⟩
    · by_cases hp0len : p0.length < p.length
      · exact False.elim (no_jump_before_p p0 k j v hp0len (heq ▸ hp_pre) hj0 hjk hp0j hq'p0j)
      · by_cases hp0eq : p0.length = p.length
        · have heq_comb : p ++ c :: rest = p0 ++ k :: v := hxeq.symm.trans heq
          have hp0_eq_p : p0 = p := by
            have htk := congrArg (List.take p.length) heq_comb
            rw [List.take_left, List.take_left' hp0eq] at htk; exact htk.symm
          subst hp0_eq_p
          have hkc : k = c := (List.cons.inj (List.append_cancel_left heq_comb.symm)).1
          subst hkc
          have hpj3 : p0 ++ [j] ∈ H3.nodes := (stage3_mem_iff B H.val σ _).mpr ⟨hp0j, ⟨q', hq'p0j⟩⟩
          have hq'pj3 : q' ∈ H3.label (p0 ++ [j]) := by rwa [stage3_label_of_mem B H.val σ hpj3]
          obtain ⟨hpj4, hpre'⟩ := push_child hj0 (List.prefix_refl _) hpj3 hq'pj3
          exact ⟨j, childRank H4.nodes p0 j, hj0, Nat.le_of_lt hjk, hpj4, rfl,
            childRank_le hpos4 p0 hj0, hpre'⟩
        · have hp_c_pre_p0 : (p ++ [c]).IsPrefix p0 := by
            have heq_comb : (p ++ [c]) ++ rest = p0 ++ k :: v := by simpa [hxeq] using heq
            have htk := congrArg (List.take (p.length + 1)) heq_comb
            rw [List.take_left' (by simp), List.take_append_of_le_length (by omega)] at htk
            exact htk ▸ List.take_prefix _ _
          have hp0j_3 : p0 ++ [j] ∈ H3.nodes := (stage3_mem_iff B H.val σ _).mpr ⟨hp0j, ⟨q', hq'p0j⟩⟩
          have hq'p0j_3 : q' ∈ H3.label (p0 ++ [j]) := by rwa [stage3_label_of_mem B H.val σ hp0j_3]
          have hp_c_pre_p0j : (p ++ [c]).IsPrefix (p0 ++ [j]) := hp_c_pre_p0.trans ⟨[j], rfl⟩
          obtain ⟨hpc4, hpre'⟩ := push_child hc0 hp_c_pre_p0j hp0j_3 hq'p0j_3
          exact ⟨c, childRank H4.nodes p c, hc0, le_rfl, hpc4, rfl, childRank_le hpos4 p hc0, hpre'⟩

lemma lemma_9_mp {Q Sigma : Type} [Fintype Q]
    (B : SemNBW Q Sigma) (α : ℕ → Sigma) (hlang : α ∈ semLanguage B) :
    ∃ (ρ : ℕ → History Q) (x : Node),
      Positive x ∧ IsTrace B α ρ ∧
      (∃ N, ∀ i ≥ N, x ∉ unstable B (ρ i) (α i)) ∧
      (∀ N, ∃ i ≥ N, x ∈ acceptingNodes B (ρ i) (α i)) := by
  obtain ⟨r, ⟨hr0, hrstep⟩, qf, hqf_acc, hqf_inf⟩ := hlang
  obtain ⟨H0, hinit, hH0_val⟩ := initialHistory_of_nonempty B ⟨r 0, hr0⟩
  have hr0_lbl : r 0 ∈ H0.val.label [] := by simp [hH0_val, initialData, hr0]
  have hnext_ex : ∀ (i : ℕ) (H : History Q), r i ∈ H.val.label [] →
      ∃ H' : History Q, successor B H (α i) = some H' ∧ r (i + 1) ∈ H'.val.label [] := by
    intro i H hri
    have hmem_bi : r (i + 1) ∈ (H.val.label []).biUnion (fun q => B.delta q (α i)) :=
      Finset.mem_biUnion.mpr ⟨r i, hri, hrstep i⟩
    have hroot4 : [] ∈ (stage4 B H.val (α i)).nodes :=
      (root_mem_stage4_iff B H (α i)).mpr ⟨r (i + 1), hmem_bi⟩
    have hv' := stage4_valid_compressed B H (α i) hroot4
    let H' : History Q := ⟨compressed (stage4 B H.val (α i)), hv'⟩
    have hsucc : successor B H (α i) = some H' := (successor_eq_some_iff B H (α i) H').mpr rfl
    have hri1 : r (i + 1) ∈ H'.val.label [] := by rw [succ_label_root B hsucc]; exact hmem_bi
    exact ⟨H', hsucc, hri1⟩
  let traceState : ∀ i : ℕ, {H : History Q // r i ∈ H.val.label []} :=
    Nat.rec ⟨H0, hr0_lbl⟩ (fun i ih =>
      ⟨Classical.choose (hnext_ex i ih.val ih.property),
       (Classical.choose_spec (hnext_ex i ih.val ih.property)).2⟩)
  let ρ : ℕ → History Q := fun i => (traceState i).val
  have hρ_lbl : ∀ i, r i ∈ (ρ i).val.label [] := fun i => (traceState i).property
  have htr : IsTrace B α ρ :=
    ⟨hinit, fun i => (Classical.choose_spec (hnext_ex i (traceState i).val (traceState i).property)).1⟩
  have hown_ex : ∀ i, ∃ x ∈ (ρ i).val.nodes, r i ∈ own (ρ i).val x := fun i => by
    obtain ⟨x, hx, _, hown⟩ := exists_own_of_mem_label (ρ i).property (ρ i).property.2.1 (hρ_lbl i)
    exact ⟨x, hx, hown⟩
  let xSeq : ℕ → Node := fun i => Classical.choose (hown_ex i)
  have hxSeq_mem : ∀ i, xSeq i ∈ (ρ i).val.nodes := fun i => (Classical.choose_spec (hown_ex i)).1
  have hxSeq_own : ∀ i, r i ∈ own (ρ i).val (xSeq i) := fun i => (Classical.choose_spec (hown_ex i)).2
  by_contra hno_wit
  have hdepth : ∀ d : ℕ, ∃ (p : Node) (N : ℕ), p.length = d ∧
      ∀ i ≥ N, p.IsPrefix (xSeq i) ∧ p ∉ unstable B (ρ i) (α i) := by
    intro d
    induction d with
    | zero =>
      refine ⟨[], 0, rfl, fun i _ => ⟨List.nil_prefix, ?_⟩⟩
      simp only [unstable, Finset.mem_filter, not_and, not_or, not_not]
      intro _; exact ⟨root_mem_stage4_of_succ B (htr.2 i), rfl⟩
    | succ d ih =>
      obtain ⟨p, N, hplen, hp_inv⟩ := ih
      have hp_pos : Positive p :=
        (ρ N).property.1.1 p ((ρ N).property.1.2.1 _ (hxSeq_mem N) p (hp_inv N le_rfl).1)
      have hnot_inf_acc : ¬ ∀ M, ∃ i ≥ M, p ∈ acceptingNodes B (ρ i) (α i) :=
        fun hacc => hno_wit ⟨ρ, p, hp_pos, htr, ⟨N, fun i hi => (hp_inv i hi).2⟩, hacc⟩
      obtain ⟨M0, hM0_pre⟩ := Classical.not_forall.mp hnot_inf_acc
      have hM0 : ∀ i ≥ M0, p ∉ acceptingNodes B (ρ i) (α i) :=
        fun i hi hpacc => hM0_pre ⟨i, hi, hpacc⟩
      let M := max N M0
      have hp_nores : ∀ i ≥ M, p ∉ resetNodes (stage3 B (ρ i).val (α i)) := by
        intro i hi hres
        have hiN : N ≤ i := le_trans (le_max_left N M0) hi
        have hiM0 : M0 ≤ i := le_trans (le_max_right N M0) hi
        obtain ⟨hpre_i, hstab_i⟩ := hp_inv i hiN
        have hp_mem_i : p ∈ (ρ i).val.nodes := (ρ i).property.1.2.1 _ (hxSeq_mem i) p hpre_i
        simp only [unstable, Finset.mem_filter, hp_mem_i, true_and, not_or, not_not] at hstab_i
        exact hM0 i hiM0 (Finset.mem_filter.mpr ⟨hp_mem_i, hres, hstab_i.1, hstab_i.2⟩)
      obtain ⟨t_acc, ht_acc_ge, ht_acc_eq⟩ := hqf_inf (M + 1)
      let i0 := t_acc - 1
      have hi0_ge : M ≤ i0 := by omega
      have hri0_acc : r (i0 + 1) ∈ B.accepting := by
        have : i0 + 1 = t_acc := by omega
        rw [this, ht_acc_eq]; exact hqf_acc
      have hstep_at : ∀ i ≥ M,
          (xSeq i = p → r (i + 1) ∈ B.accepting → p.length < (xSeq (i + 1)).length) ∧
          (∀ c rest, xSeq i = p ++ c :: rest →
            ∃ j c', 0 < j ∧ j ≤ c ∧ p ++ [j] ∈ (stage4 B (ρ i).val (α i)).nodes ∧
              c' = childRank (stage4 B (ρ i).val (α i)).nodes p j ∧ c' ≤ j ∧
              (p ++ [c']).IsPrefix (xSeq (i + 1))) := by
        intro i hi
        have hiN : N ≤ i := le_trans (le_max_left N M0) hi
        have hi1N : N ≤ i + 1 := by omega
        obtain ⟨hpre_i, hstab_i⟩ := hp_inv i hiN
        have hp_mem_i : p ∈ (ρ i).val.nodes := (ρ i).property.1.2.1 _ (hxSeq_mem i) p hpre_i
        simp only [unstable, Finset.mem_filter, hp_mem_i, true_and, not_or, not_not] at hstab_i
        exact step_owner_transition B (htr.2 i) (hrstep i) (hxSeq_mem i) (hxSeq_own i)
          (hxSeq_mem (i + 1)) (hxSeq_own (i + 1)) hpre_i (hp_inv (i + 1) hi1N).1
          hstab_i.1 hstab_i.2 (hp_nores i hi)
      let M1 := i0 + 1
      have hlen_M1 : p.length < (xSeq M1).length := by
        obtain ⟨w, hw⟩ := (hp_inv i0 (le_trans (le_max_left N M0) hi0_ge)).1
        cases w with
        | nil => exact (hstep_at i0 hi0_ge).1 (by simpa using hw.symm) hri0_acc
        | cons c rest =>
          obtain ⟨_, c', _, _, _, _, _, hpre'⟩ := (hstep_at i0 hi0_ge).2 c rest hw.symm
          have hl := hpre'.length_le; simp at hl; omega
      have hlen_all : ∀ k : ℕ, p.length < (xSeq (M1 + k)).length := by
        intro k
        induction k with
        | zero => simpa using hlen_M1
        | succ k ihk =>
          obtain ⟨w, hw⟩ := (hp_inv (M1 + k) (by omega)).1
          cases w with
          | nil => rw [← hw] at ihk; simp at ihk
          | cons c rest =>
            obtain ⟨_, c', _, _, _, _, _, hpre'⟩ := (hstep_at (M1 + k) (by omega)).2 c rest hw.symm
            have hl := hpre'.length_le; simp [Nat.add_assoc] at hl ⊢; omega
      let cSeq : ℕ → ℕ := fun k => (xSeq (M1 + k))[p.length]!
      have hcSeq_split : ∀ k : ℕ, ∃ rest, xSeq (M1 + k) = p ++ cSeq k :: rest := by
        intro k
        obtain ⟨w, hw⟩ := (hp_inv (M1 + k) (by omega)).1
        cases w with
        | nil => have hl := hlen_all k; rw [← hw] at hl; simp at hl
        | cons c rest =>
          have hc_eq : cSeq k = c := by
            simp only [cSeq, ← hw]
            have h1 : p ++ c :: rest = (p ++ [c]) ++ rest := by simp
            rw [h1, getElem!_append_left (by simp), getElem!_append_singleton_last]
          exact ⟨rest, by rw [hc_eq, hw]⟩
      have hcSeq_step : ∀ k : ℕ,
          ∃ j ≤ cSeq k, p ++ [j] ∈ (stage4 B (ρ (M1 + k)).val (α (M1 + k))).nodes ∧
            cSeq (k + 1) = childRank (stage4 B (ρ (M1 + k)).val (α (M1 + k))).nodes p j ∧
            cSeq (k + 1) ≤ j := by
        intro k
        obtain ⟨rest, hsplit⟩ := hcSeq_split k
        obtain ⟨j, c', _, hjc, hpj4, hc'rk, hc'j, hpre'⟩ :=
          (hstep_at (M1 + k) (by omega)).2 (cSeq k) rest hsplit
        have hc_next : cSeq (k + 1) = c' := by
          obtain ⟨t, ht⟩ := hpre'
          simp only [cSeq, show M1 + (k + 1) = M1 + k + 1 by omega, ← ht]
          rw [getElem!_append_left (by simp), getElem!_append_singleton_last]
        exact ⟨j, hjc, hpj4, hc_next.trans hc'rk, hc_next ▸ hc'j⟩
      have hcSeq_noninc : ∀ k, cSeq (k + 1) ≤ cSeq k := by
        intro k; obtain ⟨j, hjc, _, _, hcj⟩ := hcSeq_step k; omega
      obtain ⟨K, hK⟩ := noninc_stabilizes cSeq hcSeq_noninc
      let cStar := cSeq K
      refine ⟨p ++ [cStar], M1 + K, by simp [hplen], fun i hi => ?_⟩
      let k := i - M1
      have hkK : K ≤ k := by omega
      have hik : M1 + k = i := by omega
      have hck : cSeq k = cStar := hK k hkK
      have hck1 : cSeq (k + 1) = cStar := hK (k + 1) (by omega)
      obtain ⟨rest, hsplit⟩ := hcSeq_split k
      rw [hik, hck] at hsplit
      have hpre_next : (p ++ [cStar]).IsPrefix (xSeq i) := ⟨rest, by simpa using hsplit.symm⟩
      obtain ⟨j, hjc, hpj4, hcrk, hcj⟩ := hcSeq_step k
      rw [hik] at hpj4 hcrk; rw [hck] at hjc; rw [hck1] at hcrk hcj
      have hj_eq : j = cStar := by omega
      subst hj_eq
      obtain ⟨hpre_p_i, hstab_p_i⟩ := hp_inv i (by omega)
      have hp_mem_i : p ∈ (ρ i).val.nodes := (ρ i).property.1.2.1 _ (hxSeq_mem i) p hpre_p_i
      simp only [unstable, Finset.mem_filter, hp_mem_i, true_and, not_or, not_not] at hstab_p_i
      refine ⟨hpre_next, ?_⟩
      simp only [unstable, Finset.mem_filter, not_and, not_or, not_not]
      intro _; refine ⟨hpj4, ?_⟩
      rw [compress_concat, hstab_p_i.2, ← hcrk]
  obtain ⟨p, N, hplen, hp_inv⟩ := hdepth (Fintype.card Q)
  have hp_mem : p ∈ (ρ N).val.nodes :=
    (ρ N).property.1.2.1 _ (hxSeq_mem N) p (hp_inv N le_rfl).1
  have hlt := length_lt_card_of_mem (ρ N) hp_mem
  omega

def ReachOn {Q Sigma : Type} (B : SemNBW Q Sigma) (α : ℕ → Sigma)
    (a b : ℕ) (qa qb : Q) : Prop :=
  ∃ f : ℕ → Q, f a = qa ∧ f b = qb ∧ ∀ i, a ≤ i → i < b → f (i + 1) ∈ B.delta (f i) (α i)

def AccReachOn {Q Sigma : Type} (B : SemNBW Q Sigma) (α : ℕ → Sigma)
    (a b : ℕ) (qa qb : Q) : Prop :=
  ∃ f : ℕ → Q, f a = qa ∧ f b = qb ∧
    (∀ i, a ≤ i → i < b → f (i + 1) ∈ B.delta (f i) (α i)) ∧
    ∃ j, a < j ∧ j ≤ b ∧ f j ∈ B.accepting

lemma reachOn_refl {Q Sigma : Type} (B : SemNBW Q Sigma) (α : ℕ → Sigma) (a : ℕ) (q : Q) :
    ReachOn B α a a q q :=
  ⟨fun _ => q, rfl, rfl, fun _ h1 h2 => by omega⟩

lemma reachOn_step {Q Sigma : Type} (B : SemNBW Q Sigma) (α : ℕ → Sigma)
    {a b : ℕ} (hab : a ≤ b) {qa qb qc : Q}
    (hr : ReachOn B α a b qa qb) (hd : qc ∈ B.delta qb (α b)) :
    ReachOn B α a (b + 1) qa qc := by
  obtain ⟨f, hfa, hfb, hfstep⟩ := hr
  refine ⟨fun t => if t = b + 1 then qc else f t, ?_, by simp, ?_⟩
  · dsimp only; rw [if_neg (by omega)]; exact hfa
  · intro i hai hib; dsimp only
    by_cases hieq : i = b
    · subst hieq; rw [if_pos rfl, if_neg (by omega), hfb]; exact hd
    · rw [if_neg (by omega), if_neg (by omega)]; exact hfstep i hai (by omega)

lemma accReachOn_of_reachOn_acc {Q Sigma : Type} (B : SemNBW Q Sigma) (α : ℕ → Sigma)
    {a b : ℕ} (hab : a ≤ b) {qa qb qc : Q}
    (hr : ReachOn B α a b qa qb) (hd : qc ∈ B.delta qb (α b)) (hacc : qc ∈ B.accepting) :
    AccReachOn B α a (b + 1) qa qc := by
  obtain ⟨f, hfa, hfb, hfstep⟩ := reachOn_step B α hab hr hd
  exact ⟨f, hfa, hfb, hfstep, b + 1, by omega, le_rfl, hfb ▸ hacc⟩

lemma accReachOn_step {Q Sigma : Type} (B : SemNBW Q Sigma) (α : ℕ → Sigma)
    {a b : ℕ} (_hab : a ≤ b) {qa qb qc : Q}
    (hr : AccReachOn B α a b qa qb) (hd : qc ∈ B.delta qb (α b)) :
    AccReachOn B α a (b + 1) qa qc := by
  obtain ⟨f, hfa, hfb, hfstep, j, haj, hjb, hfj⟩ := hr
  have hab' : a < b := lt_of_lt_of_le haj hjb
  refine ⟨fun t => if t = b + 1 then qc else f t, ?_, by simp, ?_, j, haj, by omega, ?_⟩
  · dsimp only; rw [if_neg (by omega)]; exact hfa
  · intro i hai hib; dsimp only
    by_cases hieq : i = b
    · subst hieq; rw [if_pos rfl, if_neg (by omega), hfb]; exact hd
    · rw [if_neg (by omega), if_neg (by omega)]; exact hfstep i hai (by omega)
  · dsimp only; rw [if_neg (by omega)]; exact hfj

lemma root_reach_of_trace {Q Sigma : Type} {B : SemNBW Q Sigma} {α : ℕ → Sigma}
    {ρ : ℕ → History Q} (htr : IsTrace B α ρ) :
    ∀ m : ℕ, ∀ q ∈ (ρ m).val.label [], ∃ q0 ∈ B.initial, ReachOn B α 0 m q0 q
  | 0, q, hq => by
    have hinit := htr.1
    unfold initialHistory asHistory at hinit
    split_ifs at hinit with hv
    have h0 : ρ 0 = ⟨initialData B, hv⟩ := Option.some.inj hinit.symm
    rw [h0] at hq; simp only [initialData, ↓reduceIte] at hq
    exact ⟨q, hq, reachOn_refl B α 0 q⟩
  | m + 1, q, hq => by
    rw [succ_label_root B (htr.2 m)] at hq
    obtain ⟨q', hq', hd⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨q0, hq0, hr⟩ := root_reach_of_trace htr m q' hq'
    exact ⟨q0, hq0, reachOn_step B α (Nat.zero_le m) hr hd⟩

inductive LayerReach {Q : Type} (L : ℕ → Finset Q) (R : ℕ → Q → Q → Prop) :
    ℕ → ℕ → Q → Q → Prop where
  | refl {k : ℕ} {q : Q} (hq : q ∈ L k) : LayerReach L R k 0 q q
  | step {k d : ℕ} {q q' q'' : Q}
      (h1 : LayerReach L R k d q q')
      (h2 : R (k + d) q' q'')
      (h3 : q'' ∈ L (k + d + 1)) : LayerReach L R k (d + 1) q q''

lemma layerReach_exists_pred {Q : Type} {L : ℕ → Finset Q} {R : ℕ → Q → Q → Prop}
    (hpred : ∀ k, ∀ q'' ∈ L (k + 1), ∃ q' ∈ L k, R k q' q'') :
    ∀ k d, ∀ q'' ∈ L (k + d), ∃ q ∈ L k, LayerReach L R k d q q''
  | _, 0, q'', hq'' => ⟨q'', hq'', LayerReach.refl hq''⟩
  | k, d + 1, q'', hq'' => by
    obtain ⟨q', hq', hr⟩ := hpred (k + d) q'' hq''
    obtain ⟨q, hq, hlr⟩ := layerReach_exists_pred hpred k d q' hq'
    exact ⟨q, hq, LayerReach.step hlr hr hq''⟩

lemma layerReach_truncate {Q : Type} {L : ℕ → Finset Q} {R : ℕ → Q → Q → Prop}
    {k : ℕ} : ∀ {d e : ℕ} {q w : Q},
      LayerReach L R k (d + e) q w → ∃ u, LayerReach L R k d q u
  | _, 0, _, w, h => ⟨w, h⟩
  | _, _ + 1, _, _, h => by cases h with | step h1 _ _ => exact layerReach_truncate h1

lemma layerReach_uncons {Q : Type} {L : ℕ → Finset Q} {R : ℕ → Q → Q → Prop}
    {k : ℕ} : ∀ {d : ℕ} {q w : Q},
      LayerReach L R k (d + 1) q w →
      ∃ q1 ∈ L (k + 1), R k q q1 ∧ LayerReach L R (k + 1) d q1 w
  | 0, _, w, h => by
    cases h with
    | step h1 h2 h3 =>
      cases h1 with
      | refl _ =>
        exact ⟨w, by simpa using h3, by simpa using h2, LayerReach.refl (by simpa using h3)⟩
  | d + 1, _, w, h => by
    cases h with
    | step h1 h2 h3 =>
      obtain ⟨q1, hq1, hr1, hlr⟩ := layerReach_uncons h1
      refine ⟨q1, hq1, hr1, LayerReach.step hlr ?_ ?_⟩
      · simpa [Nat.add_assoc, Nat.add_comm 1 d] using h2
      · simpa [Nat.add_assoc, Nat.add_comm 1 d] using h3

lemma konig_layers {Q : Type} [Fintype Q]
    (L : ℕ → Finset Q) (R : ℕ → Q → Q → Prop)
    (hne : ∀ k, (L k).Nonempty)
    (hpred : ∀ k, ∀ q'' ∈ L (k + 1), ∃ q' ∈ L k, R k q' q'') :
    ∃ seq : ℕ → Q, (∀ k, seq k ∈ L k) ∧ (∀ k, R k (seq k) (seq (k + 1))) := by
  let Good : ℕ → Q → Prop := fun k q => q ∈ L k ∧ ∀ d, ∃ w, LayerReach L R k d q w
  have hGood0 : ∃ q0, Good 0 q0 := by
    have hex_d : ∀ d : ℕ, ∃ q ∈ L 0, ∃ w, LayerReach L R 0 d q w := by
      intro d
      obtain ⟨w, hw⟩ := hne d
      obtain ⟨q, hq, hlr⟩ := layerReach_exists_pred hpred 0 d w (by simpa using hw)
      exact ⟨q, hq, w, hlr⟩
    have : Nonempty Q := ⟨Classical.choose (hne 0)⟩
    let g : ℕ → Q := fun d => Classical.choose (hex_d d)
    obtain ⟨q0, hq0_inf⟩ := Finite.exists_infinite_fiber g
    have hq0_set : (g ⁻¹' {q0}).Infinite := Set.infinite_coe_iff.mp hq0_inf
    obtain ⟨d0, hd0⟩ := hq0_set.nonempty
    have hd0_eq : Classical.choose (hex_d d0) = q0 := hd0
    refine ⟨q0, hd0_eq ▸ (Classical.choose_spec (hex_d d0)).1, fun d => ?_⟩
    obtain ⟨d', hd'_mem, hd'_not_lt⟩ := (hq0_set.sdiff (Set.finite_lt_nat d)).nonempty
    have hd'_ge : d ≤ d' := Nat.le_of_not_lt hd'_not_lt
    have hd'_eq : Classical.choose (hex_d d') = q0 := hd'_mem
    obtain ⟨w, hlr⟩ := (Classical.choose_spec (hex_d d')).2
    rw [hd'_eq] at hlr
    have hsplit : d' = d + (d' - d) := by omega
    rw [hsplit] at hlr
    exact layerReach_truncate hlr
  have hGood_step : ∀ k q, Good k q → ∃ q1, Good (k + 1) q1 ∧ R k q q1 := by
    intro k q ⟨_, hreach⟩
    have hex_d : ∀ d : ℕ, ∃ q1 ∈ L (k + 1), R k q q1 ∧ ∃ w, LayerReach L R (k + 1) d q1 w := by
      intro d
      obtain ⟨w, hlr⟩ := hreach (d + 1)
      obtain ⟨q1, hq1, hr, hlr'⟩ := layerReach_uncons hlr
      exact ⟨q1, hq1, hr, w, hlr'⟩
    have : Nonempty Q := ⟨Classical.choose (hne 0)⟩
    let h : ℕ → Q := fun d => Classical.choose (hex_d d)
    obtain ⟨q1, hq1_inf⟩ := Finite.exists_infinite_fiber h
    have hq1_set : (h ⁻¹' {q1}).Infinite := Set.infinite_coe_iff.mp hq1_inf
    obtain ⟨d0, hd0⟩ := hq1_set.nonempty
    have hd0_eq : Classical.choose (hex_d d0) = q1 := hd0
    have hspec0 := Classical.choose_spec (hex_d d0)
    refine ⟨q1, ⟨hd0_eq ▸ hspec0.1, fun d => ?_⟩, hd0_eq ▸ hspec0.2.1⟩
    obtain ⟨d', hd'_mem, hd'_not_lt⟩ := (hq1_set.sdiff (Set.finite_lt_nat d)).nonempty
    have hd'_ge : d ≤ d' := Nat.le_of_not_lt hd'_not_lt
    have hd'_eq : Classical.choose (hex_d d') = q1 := hd'_mem
    obtain ⟨w, hlr⟩ := (Classical.choose_spec (hex_d d')).2.2
    rw [hd'_eq] at hlr
    have hsplit : d' = d + (d' - d) := by omega
    rw [hsplit] at hlr
    exact layerReach_truncate hlr
  let gSeq : ∀ k : ℕ, {q : Q // Good k q} :=
    Nat.rec ⟨Classical.choose hGood0, Classical.choose_spec hGood0⟩
      (fun k ih =>
        ⟨Classical.choose (hGood_step k ih.val ih.property),
         (Classical.choose_spec (hGood_step k ih.val ih.property)).1⟩)
  exact ⟨fun k => (gSeq k).val, fun k => (gSeq k).property.1,
    fun k => (Classical.choose_spec (hGood_step k (gSeq k).val (gSeq k).property)).2⟩

lemma lemma_9_mpr {Q Sigma : Type} [Fintype Q]
    (B : SemNBW Q Sigma) (α : ℕ → Sigma)
    {ρ : ℕ → History Q} {x : Node}
    (htr : IsTrace B α ρ)
    (hstab_ex : ∃ N, ∀ i ≥ N, x ∉ unstable B (ρ i) (α i))
    (hacc_inf : ∀ N, ∃ i ≥ N, x ∈ acceptingNodes B (ρ i) (α i)) :
    α ∈ semLanguage B := by
  obtain ⟨N0, hstab⟩ := hstab_ex
  let tSeq : ℕ → ℕ :=
    Nat.rec (Classical.choose (hacc_inf N0))
      (fun _ prev => Classical.choose (hacc_inf (prev + 1)))
  have ht_succ : ∀ k, tSeq (k + 1) = Classical.choose (hacc_inf (tSeq k + 1)) := fun _ => rfl
  have ht0_ge : N0 ≤ tSeq 0 := (Classical.choose_spec (hacc_inf N0)).1
  have ht_acc : ∀ k, x ∈ acceptingNodes B (ρ (tSeq k)) (α (tSeq k)) := by
    intro k
    cases k with
    | zero => exact (Classical.choose_spec (hacc_inf N0)).2
    | succ k => exact (Classical.choose_spec (hacc_inf (tSeq k + 1))).2
  have ht_lt : ∀ k, tSeq k < tSeq (k + 1) := fun k => by
    rw [ht_succ k]; have := (Classical.choose_spec (hacc_inf (tSeq k + 1))).1; omega
  have hx_mem_t0 : x ∈ (ρ (tSeq 0)).val.nodes := (Finset.mem_filter.mp (ht_acc 0)).1
  have hx_persist : ∀ d : ℕ,
      let i := tSeq 0 + d
      x ∈ (ρ i).val.nodes ∧
      x ∈ (stage4 B (ρ i).val (α i)).nodes ∧
      compress (stage4 B (ρ i).val (α i)).nodes x = x ∧
      (ρ (i + 1)).val.label x = (stage3 B (ρ i).val (α i)).label x := by
    intro d
    induction d with
    | zero =>
      simp only [Nat.add_zero]
      have hst := hstab (tSeq 0) ht0_ge
      simp only [unstable, Finset.mem_filter, hx_mem_t0, true_and, not_or, not_not] at hst
      have hsucc_eq :=
        (successor_eq_some_iff B (ρ (tSeq 0)) (α (tSeq 0)) (ρ (tSeq 0 + 1))).mp (htr.2 (tSeq 0))
      have hpref4 : ∀ u ∈ (stage4 B (ρ (tSeq 0)).val (α (tSeq 0))).nodes, ∀ p, p.IsPrefix u →
          p ∈ (stage4 B (ρ (tSeq 0)).val (α (tSeq 0))).nodes :=
        fun u hu p hp => stage4_prefix_closed B (ρ (tSeq 0)).property (α (tSeq 0)) hu hp
      have hlbl := compressed_label_of_mem hpref4 hst.1
      rw [hst.2] at hlbl
      exact ⟨hx_mem_t0, hst.1, hst.2, by rw [hsucc_eq, hlbl, stage4_label_of_mem B _ _ hst.1]⟩
    | succ d ih =>
      obtain ⟨_, hx4_prev, hxcomp_prev, _⟩ := ih
      let ip := tSeq 0 + d
      let i := tSeq 0 + (d + 1)
      have hsucc_prev := (successor_eq_some_iff B (ρ ip) (α ip) (ρ (ip + 1))).mp (htr.2 ip)
      have hx_mem_next : x ∈ (ρ i).val.nodes := by
        have : i = ip + 1 := by omega
        rw [this, hsucc_prev]
        exact Finset.mem_image.mpr ⟨x, hx4_prev, hxcomp_prev⟩
      have hst := hstab i (by omega)
      simp only [unstable, Finset.mem_filter, hx_mem_next, true_and, not_or, not_not] at hst
      have hsucc_eq := (successor_eq_some_iff B (ρ i) (α i) (ρ (i + 1))).mp (htr.2 i)
      have hpref4 : ∀ u ∈ (stage4 B (ρ i).val (α i)).nodes, ∀ p, p.IsPrefix u →
          p ∈ (stage4 B (ρ i).val (α i)).nodes :=
        fun u hu p hp => stage4_prefix_closed B (ρ i).property (α i) hu hp
      have hlbl := compressed_label_of_mem hpref4 hst.1
      rw [hst.2] at hlbl
      exact ⟨hx_mem_next, hst.1, hst.2, by rw [hsucc_eq, hlbl, stage4_label_of_mem B _ _ hst.1]⟩
  have hx_at : ∀ i ≥ tSeq 0,
      x ∈ (ρ i).val.nodes ∧
      x ∈ (stage4 B (ρ i).val (α i)).nodes ∧
      compress (stage4 B (ρ i).val (α i)).nodes x = x ∧
      (ρ (i + 1)).val.label x = (stage3 B (ρ i).val (α i)).label x :=
    fun i hi => by simpa [show tSeq 0 + (i - tSeq 0) = i by omega] using hx_persist (i - tSeq 0)
  let sSeq : ℕ → ℕ := fun k => tSeq k + 1
  have hs_lt : ∀ k, sSeq k < sSeq (k + 1) := fun k => by have := ht_lt k; simp [sSeq]; omega
  have ht0_le_tk : ∀ k, tSeq 0 ≤ tSeq k := by
    intro k; induction k with | zero => exact le_rfl | succ k ih => have := ht_lt k; omega
  have hx_leaf_after_acc : ∀ k, children (ρ (sSeq k)).val.nodes x = ∅ := by
    intro k
    have hacc_k := ht_acc k
    simp only [acceptingNodes, Finset.mem_filter] at hacc_k
    obtain ⟨_, hres_k, hx4_k, hxcomp_k⟩ := hacc_k
    have hsucc_eq :=
      (successor_eq_some_iff B (ρ (tSeq k)) (α (tSeq k)) (ρ (sSeq k))).mp (htr.2 (tSeq k))
    have hpref4 : ∀ u ∈ (stage4 B (ρ (tSeq k)).val (α (tSeq k))).nodes, ∀ p, p.IsPrefix u →
        p ∈ (stage4 B (ρ (tSeq k)).val (α (tSeq k))).nodes :=
      fun u hu p hp => stage4_prefix_closed B (ρ (tSeq k)).property (α (tSeq k)) hu hp
    have hch := compressed_children_of_mem hpref4 hx4_k
    rw [hxcomp_k, stage4_children_of_reset B _ _ hres_k] at hch
    rw [hsucc_eq, hch]; simp
  have hseg_inv : ∀ (k d : ℕ),
      (∀ q ∈ (ρ (sSeq k + d)).val.label x,
        ∃ qa ∈ (ρ (sSeq k)).val.label x, ReachOn B α (sSeq k) (sSeq k + d) qa q) ∧
      (∀ y ∈ children (ρ (sSeq k + d)).val.nodes x, ∀ q ∈ (ρ (sSeq k + d)).val.label y,
        ∃ qa ∈ (ρ (sSeq k)).val.label x, AccReachOn B α (sSeq k) (sSeq k + d) qa q) := by
    intro k d
    induction d with
    | zero =>
      simp only [Nat.add_zero]
      refine ⟨fun q hq => ⟨q, hq, reachOn_refl B α (sSeq k) q⟩, ?_⟩
      intro y hy; rw [hx_leaf_after_acc k] at hy; simp at hy
    | succ d ih =>
      let a := sSeq k; let m := a + d
      have hm_ge_t0 : tSeq 0 ≤ m := by have := ht0_le_tk k; simp [m, a, sSeq]; omega
      obtain ⟨hx_m, hx4_m, hxcomp_m, hlbl_next⟩ := hx_at m hm_ge_t0
      have hx3_m : x ∈ (stage3 B (ρ m).val (α m)).nodes :=
        ((stage4_mem_iff B (ρ m).val (α m) x).mp hx4_m).1
      have hsub31 : ∀ u ∈ (stage3 B (ρ m).val (α m)).nodes,
          (stage3 B (ρ m).val (α m)).label u ⊆ (expand B (ρ m).val (α m)).label u := by
        intro u hu q hq
        rw [stage3_label_of_mem B _ _ hu] at hq
        exact (Finset.mem_filter.mp hq).1
      have hm1_eq : sSeq k + (d + 1) = m + 1 := by simp [m, a, Nat.add_assoc]
      refine ⟨?_, ?_⟩
      · intro q hq
        rw [hm1_eq, hlbl_next] at hq
        have hq1 := hsub31 x hx3_m hq
        rw [expand_label_old B (ρ m).val (α m) hx_m] at hq1
        obtain ⟨q', hq'x, hd⟩ := Finset.mem_biUnion.mp hq1
        obtain ⟨qa, hqa, hr⟩ := ih.1 q' hq'x
        rw [hm1_eq]
        exact ⟨qa, hqa, reachOn_step B α (Nat.le_add_right a d) hr hd⟩
      · intro y' hy' q hq
        rw [hm1_eq] at hy' hq ⊢
        have hsucc_eq := (successor_eq_some_iff B (ρ m) (α m) (ρ (m + 1))).mp (htr.2 m)
        have hpref4 : ∀ u ∈ (stage4 B (ρ m).val (α m)).nodes, ∀ p, p.IsPrefix u →
            p ∈ (stage4 B (ρ m).val (α m)).nodes :=
          fun u hu p hp => stage4_prefix_closed B (ρ m).property (α m) hu hp
        have hch_eq := compressed_children_of_mem hpref4 hx4_m
        rw [hxcomp_m] at hch_eq
        rw [hsucc_eq, hch_eq] at hy'
        obtain ⟨y, hy_ch4, rfl⟩ := Finset.mem_image.mp hy'
        simp only [children, Finset.mem_filter] at hy_ch4
        obtain ⟨hy4, j, rfl⟩ := hy_ch4
        have hy3 : x ++ [j] ∈ (stage3 B (ρ m).val (α m)).nodes :=
          ((stage4_mem_iff B (ρ m).val (α m) _).mp hy4).1
        rw [hsucc_eq, compressed_label_of_mem hpref4 hy4, stage4_label_of_mem B _ _ hy4] at hq
        have hq1 : q ∈ (expand B (ρ m).val (α m)).label (x ++ [j]) := hsub31 _ hy3 hq
        have hy1 : x ++ [j] ∈ (expand B (ρ m).val (α m)).nodes :=
          ((stage3_mem_iff B (ρ m).val (α m) _).mp hy3).1
        rcases (expand_mem_iff B (ρ m).val (α m) (x ++ [j])).mp hy1 with hy_old | ⟨z, hz_old, heq⟩
        · rw [expand_label_old B (ρ m).val (α m) hy_old] at hq1
          obtain ⟨q', hq'y, hd⟩ := Finset.mem_biUnion.mp hq1
          have hy_ch_m : x ++ [j] ∈ children (ρ m).val.nodes x := by simp [children, hy_old]
          obtain ⟨qa, hqa, har⟩ := ih.2 (x ++ [j]) hy_ch_m q' hq'y
          exact ⟨qa, hqa, accReachOn_step B α (Nat.le_add_right a d) har hd⟩
        · obtain ⟨rfl, rfl⟩ := append_singleton_inj heq
          rw [expand_label_new B (ρ m).val (α m) hz_old] at hq1
          obtain ⟨hq_bi, hq_acc⟩ := Finset.mem_inter.mp hq1
          obtain ⟨q', hq'x, hd⟩ := Finset.mem_biUnion.mp hq_bi
          obtain ⟨qa, hqa, hr⟩ := ih.1 q' hq'x
          exact ⟨qa, hqa, accReachOn_of_reachOn_acc B α (Nat.le_add_right a d) hr hd hq_acc⟩
  let L : ℕ → Finset Q := fun k => (ρ (sSeq k)).val.label x
  have hL_ne : ∀ k, (L k).Nonempty := by
    intro k
    have hs_ge : tSeq 0 ≤ sSeq k := by have := ht0_le_tk k; simp [sSeq]; omega
    exact (ρ (sSeq k)).property.2.2.2.1 x (hx_at (sSeq k) hs_ge).1
  have hL_pred : ∀ k, ∀ q'' ∈ L (k + 1),
      ∃ q' ∈ L k, AccReachOn B α (sSeq k) (sSeq (k + 1)) q' q'' := by
    intro k q'' hq''
    let m := tSeq (k + 1)
    have ha_le_m : sSeq k ≤ m := by have := ht_lt k; simp [sSeq, m]; omega
    let d := m - sSeq k
    have hm_eq : sSeq k + d = m := by omega
    obtain ⟨ih1, ih2⟩ := hseg_inv k d
    rw [hm_eq] at ih1 ih2
    obtain ⟨_, _, _, hlbl_next⟩ := hx_at m (ht0_le_tk (k + 1))
    have hacc_m := ht_acc (k + 1)
    simp only [acceptingNodes, Finset.mem_filter] at hacc_m
    have hres_m : x ∈ resetNodes (stage3 B (ρ m).val (α m)) := hacc_m.2.1
    have hres_eq : (stage3 B (ρ m).val (α m)).label x = childLabels (stage3 B (ρ m).val (α m)) x :=
      (Finset.mem_filter.mp hres_m).2
    have hq''_3 : q'' ∈ childLabels (stage3 B (ρ m).val (α m)) x := by
      change q'' ∈ (ρ (m + 1)).val.label x at hq''
      rwa [hlbl_next, hres_eq] at hq''
    obtain ⟨y, hy_ch3, hq''y3⟩ := Finset.mem_biUnion.mp hq''_3
    simp only [children, Finset.mem_filter] at hy_ch3
    obtain ⟨hy3, j, rfl⟩ := hy_ch3
    have hq''y1 : q'' ∈ (expand B (ρ m).val (α m)).label (x ++ [j]) := by
      rw [stage3_label_of_mem B _ _ hy3] at hq''y3
      exact (Finset.mem_filter.mp hq''y3).1
    have hy1 : x ++ [j] ∈ (expand B (ρ m).val (α m)).nodes :=
      ((stage3_mem_iff B (ρ m).val (α m) _).mp hy3).1
    have hs_next : sSeq (k + 1) = m + 1 := rfl
    rw [hs_next]
    rcases (expand_mem_iff B (ρ m).val (α m) (x ++ [j])).mp hy1 with hy_old | ⟨z, hz_old, heq⟩
    · rw [expand_label_old B (ρ m).val (α m) hy_old] at hq''y1
      obtain ⟨q_mid, hq_mid, hd⟩ := Finset.mem_biUnion.mp hq''y1
      have hy_ch_m : x ++ [j] ∈ children (ρ m).val.nodes x := by simp [children, hy_old]
      obtain ⟨qa, hqa, har⟩ := ih2 (x ++ [j]) hy_ch_m q_mid hq_mid
      exact ⟨qa, hqa, accReachOn_step B α ha_le_m har hd⟩
    · obtain ⟨rfl, rfl⟩ := append_singleton_inj heq
      rw [expand_label_new B (ρ m).val (α m) hz_old] at hq''y1
      obtain ⟨hq_bi, hq_acc⟩ := Finset.mem_inter.mp hq''y1
      obtain ⟨q_mid, hq_mid, hd⟩ := Finset.mem_biUnion.mp hq_bi
      obtain ⟨qa, hqa, hr⟩ := ih1 q_mid hq_mid
      exact ⟨qa, hqa, accReachOn_of_reachOn_acc B α ha_le_m hr hd hq_acc⟩
  obtain ⟨qSeq, hqSeq_mem, hqSeq_step⟩ :=
    konig_layers L (fun k q1 q2 => AccReachOn B α (sSeq k) (sSeq (k + 1)) q1 q2) hL_ne hL_pred
  have hq0_root : qSeq 0 ∈ (ρ (sSeq 0)).val.label [] := by
    have hx_s0 : x ∈ (ρ (sSeq 0)).val.nodes := (hx_at (sSeq 0) (by simp [sSeq])).1
    exact label_sub_of_prefix (ρ (sSeq 0)).property [] x (by simpa using hx_s0)
      (by simpa using hqSeq_mem 0)
  obtain ⟨qInit, hqInit, fInit, hfInit0, hfInits0, hfInit_step⟩ :=
    root_reach_of_trace htr (sSeq 0) (qSeq 0) hq0_root
  let fSeg : ℕ → ℕ → Q := fun k => Classical.choose (hqSeq_step k)
  have hfSeg_spec : ∀ k,
      fSeg k (sSeq k) = qSeq k ∧
      fSeg k (sSeq (k + 1)) = qSeq (k + 1) ∧
      (∀ i, sSeq k ≤ i → i < sSeq (k + 1) → fSeg k (i + 1) ∈ B.delta (fSeg k i) (α i)) ∧
      ∃ j, sSeq k < j ∧ j ≤ sSeq (k + 1) ∧ fSeg k j ∈ B.accepting :=
    fun k => Classical.choose_spec (hqSeq_step k)
  have hs_mono : StrictMono sSeq := strictMono_nat_of_lt_succ hs_lt
  have hs_ge_id : ∀ k, k ≤ sSeq k := by
    intro k; induction k with | zero => omega | succ k ih => have := hs_lt k; omega
  let segSet : ℕ → Finset ℕ := fun i => (Finset.range (i + 1)).filter (fun k => sSeq k ≤ i)
  have hsegSet_ne : ∀ {i : ℕ}, sSeq 0 ≤ i → (segSet i).Nonempty := fun {i} hi =>
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hi⟩⟩
  let idxOf : ∀ (i : ℕ), sSeq 0 ≤ i → ℕ := fun i hi => (segSet i).max' (hsegSet_ne hi)
  have hidx_bounds : ∀ {i : ℕ} (hi : sSeq 0 ≤ i),
      sSeq (idxOf i hi) ≤ i ∧ i < sSeq (idxOf i hi + 1) := by
    intro i hi
    have hmem := Finset.max'_mem (segSet i) (hsegSet_ne hi)
    refine ⟨(Finset.mem_filter.mp hmem).2, ?_⟩
    by_contra hnot_lt
    have hge : sSeq (idxOf i hi + 1) ≤ i := Nat.le_of_not_lt hnot_lt
    have hk1_le_i : idxOf i hi + 1 ≤ i := le_trans (hs_ge_id _) hge
    have hk1_mem : idxOf i hi + 1 ∈ segSet i :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hge⟩
    have hmax := Finset.le_max' (segSet i) (idxOf i hi + 1) hk1_mem
    change idxOf i hi + 1 ≤ idxOf i hi at hmax; omega
  have hidx_eq : ∀ {i k : ℕ} (hi : sSeq 0 ≤ i),
      sSeq k ≤ i → i < sSeq (k + 1) → idxOf i hi = k := by
    intro i k hi h1 h2
    obtain ⟨b1, b2⟩ := hidx_bounds hi
    rcases lt_trichotomy (idxOf i hi) k with hlt | heq | hgt
    · have := hs_mono.monotone (show idxOf i hi + 1 ≤ k by omega); omega
    · exact heq
    · have := hs_mono.monotone (show k + 1 ≤ idxOf i hi by omega); omega
  let run : ℕ → Q := fun i =>
    if hi : sSeq 0 ≤ i then fSeg (idxOf i hi) i else fInit i
  have hrun_at_s : ∀ k, run (sSeq k) = qSeq k := by
    intro k
    have hi : sSeq 0 ≤ sSeq k := hs_mono.monotone (Nat.zero_le k)
    simp only [run, dif_pos hi]; rw [hidx_eq hi le_rfl (hs_lt k)]; exact (hfSeg_spec k).1
  have hrun_in_seg : ∀ k i, sSeq k ≤ i → i < sSeq (k + 1) → run i = fSeg k i := by
    intro k i h1 h2
    have hi : sSeq 0 ≤ i := le_trans (hs_mono.monotone (Nat.zero_le k)) h1
    simp only [run, dif_pos hi, hidx_eq hi h1 h2]
  have hisRun : IsRun B α run := by
    refine ⟨?_, ?_⟩
    · simp only [run, dif_neg (show ¬ sSeq 0 ≤ 0 by simp [sSeq])]; rw [hfInit0]; exact hqInit
    · intro i
      by_cases hi : sSeq 0 ≤ i
      · obtain ⟨hk1, hk2⟩ := hidx_bounds hi
        rw [hrun_in_seg (idxOf i hi) i hk1 hk2]
        by_cases hi1 : i + 1 < sSeq (idxOf i hi + 1)
        · rw [hrun_in_seg (idxOf i hi) (i + 1) (Nat.le_trans hk1 (Nat.le_succ i)) hi1]
          exact (hfSeg_spec (idxOf i hi)).2.2.1 i hk1 hk2
        · have heq : i + 1 = sSeq (idxOf i hi + 1) := by omega
          rw [heq, hrun_at_s (idxOf i hi + 1), ← (hfSeg_spec (idxOf i hi)).2.1, ← heq]
          exact (hfSeg_spec (idxOf i hi)).2.2.1 i hk1 hk2
      · have hilt : i < sSeq 0 := Nat.lt_of_not_le hi
        simp only [run, dif_neg hi]
        by_cases hi1 : i + 1 < sSeq 0
        · rw [dif_neg (show ¬ sSeq 0 ≤ i + 1 by omega)]
          exact hfInit_step i (Nat.zero_le i) hilt
        · have heq : i + 1 = sSeq 0 := by omega
          have hrun_s0 := hrun_at_s 0
          simp only [run] at hrun_s0
          rw [heq, hrun_s0, ← hfInits0, ← heq]
          exact hfInit_step i (Nat.zero_le i) hilt
  have hwit_ex : ∀ k, ∃ j, sSeq k < j ∧ j ≤ sSeq (k + 1) ∧ run j ∈ B.accepting := by
    intro k
    obtain ⟨j, hj1, hj2, hjacc⟩ := (hfSeg_spec k).2.2.2
    refine ⟨j, hj1, hj2, ?_⟩
    by_cases hjlt : j < sSeq (k + 1)
    · rw [hrun_in_seg k j (Nat.le_of_lt hj1) hjlt]; exact hjacc
    · have hjeq : j = sSeq (k + 1) := by omega
      rw [hjeq, hrun_at_s (k + 1), ← (hfSeg_spec k).2.1, ← hjeq]; exact hjacc
  let witIdx : ℕ → ℕ := fun k => Classical.choose (hwit_ex k)
  have hwit_spec : ∀ k,
      sSeq k < witIdx k ∧ witIdx k ≤ sSeq (k + 1) ∧ run (witIdx k) ∈ B.accepting :=
    fun k => Classical.choose_spec (hwit_ex k)
  have : Nonempty Q := ⟨run 0⟩
  obtain ⟨qf, hqf_inf⟩ := Finite.exists_infinite_fiber (fun k => run (witIdx k))
  have hqf_set : ((fun k => run (witIdx k)) ⁻¹' {qf}).Infinite := Set.infinite_coe_iff.mp hqf_inf
  obtain ⟨k0, hk0⟩ := hqf_set.nonempty
  have hqf_acc : qf ∈ B.accepting := by
    have heq : run (witIdx k0) = qf := hk0
    exact heq ▸ (hwit_spec k0).2.2
  refine ⟨run, hisRun, qf, hqf_acc, fun N => ?_⟩
  obtain ⟨k, hk_mem, hk_not_lt⟩ := (hqf_set.sdiff (Set.finite_lt_nat N)).nonempty
  have hk_ge : N ≤ k := Nat.le_of_not_lt hk_not_lt
  have hk_eq : run (witIdx k) = qf := hk_mem
  have hwit_ge : N ≤ witIdx k := by have := hs_ge_id k; have := (hwit_spec k).1; omega
  exact ⟨witIdx k, hwit_ge, hk_eq⟩

end
end SemanticHistory

/-! #### Finite node universe `nodesUniv` and modular `Primrec` history-tree transition -/

section ExecutableHistory

def nodesUniv (n : ℕ) : List Node :=
  dedupLeft ([] :: (List.range (n + 1)).flatMap
    (fun len => wordsOf ((List.range (n + 1)).map (· + 1)) len))

lemma primrec_nodesUniv : Primrec nodesUniv := by
  have hpos : Primrec (fun n : ℕ => (List.range (n + 1)).map (· + 1)) :=
    Primrec.list_map (Primrec.list_range.comp Primrec.succ) (Primrec.succ.comp Primrec.snd).to₂
  have hraw : Primrec (fun n : ℕ => (List.range (n + 1)).flatMap
      (fun len => wordsOf ((List.range (n + 1)).map (· + 1)) len)) :=
    Primrec.list_flatMap (Primrec.list_range.comp Primrec.succ)
      (wordsOf_primrec.comp (hpos.comp Primrec.fst) Primrec.snd).to₂
  exact dedupLeft_primrec.comp (Primrec.list_cons.comp (Primrec.const []) hraw)

lemma nodesUniv_nodup (n : ℕ) : (nodesUniv n).Nodup := nodup_dedupLeft _

lemma nodesUniv_pos (n : ℕ) : 0 < (nodesUniv n).length := dedupLeft_cons_pos _ _

lemma mem_nodesUniv_of_history {n : ℕ} (H : History (Fin (n + 1))) {x : Node}
    (hx : x ∈ H.val.nodes) : x ∈ nodesUniv n := by
  rw [nodesUniv, mem_dedupLeft, List.mem_cons]
  right; rw [List.mem_flatMap]
  have hlen : x.length < n + 1 := by simpa using length_lt_card_of_mem H hx
  refine ⟨x.length, List.mem_range.mpr hlen, ?_⟩
  rw [mem_wordsOf_iff]
  refine ⟨rfl, fun i hi => ?_⟩
  obtain ⟨hi0, hile⟩ := entry_le_card_of_mem H hx hi
  simp only [Fintype.card_fin] at hile
  rw [List.mem_map]
  exact ⟨i - 1, List.mem_range.mpr (by omega), by omega⟩

abbrev TreeCode : Type := List (Node × List ℕ)

def tLabel (c : TreeCode) (x : Node) : List ℕ :=
  c.foldr (fun e acc => if e.1 = x then e.2 else acc) []

lemma tLabel_nil (x : Node) : tLabel [] x = [] := rfl

lemma tLabel_cons (e : Node × List ℕ) (es : TreeCode) (x : Node) :
    tLabel (e :: es) x = if e.1 = x then e.2 else tLabel es x := rfl

lemma primrec₂_tLabel : Primrec₂ tLabel :=
  Primrec.list_foldr Primrec.fst (Primrec.const [])
    (Primrec.ite
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

lemma tLabel_map_of_mem {dom : List Node} (hnodup : dom.Nodup) (f : Node → List ℕ)
    {x : Node} (hx : x ∈ dom) :
    tLabel (dom.map fun y => (y, f y)) x = f x := by
  induction dom with
  | nil => cases hx
  | cons y ys ih =>
    obtain ⟨hynot, hys⟩ := List.nodup_cons.mp hnodup
    rw [List.map_cons, tLabel_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · simp
    · have hne : y ≠ x := fun heq => hynot (heq ▸ hmem)
      simp [hne, ih hys hmem]

lemma tLabel_map_of_notMem {dom : List Node} (f : Node → List ℕ) {x : Node} (hx : x ∉ dom) :
    tLabel (dom.map fun y => (y, f y)) x = [] := by
  induction dom with
  | nil => rfl
  | cons y ys ih =>
    have hy : y ≠ x := fun heq => hx (heq ▸ List.mem_cons_self)
    have hys : x ∉ ys := fun hm => hx (List.mem_cons_of_mem _ hm)
    rw [List.map_cons, tLabel_cons]
    simp [hy, ih hys]

noncomputable def encodeHistory (n : ℕ) (H : History (Fin (n + 1))) : TreeCode :=
  let dom := (nodesUniv n).filter (fun x =>
    @decide (x ∈ H.val.nodes) (Classical.propDecidable _))
  dom.map (fun x => (x, encodeSet (H.val.label x)))

lemma encodeHistory_fst_mem_iff (n : ℕ) (H : History (Fin (n + 1))) (x : Node) :
    x ∈ (encodeHistory n H).map Prod.fst ↔ x ∈ H.val.nodes := by
  unfold encodeHistory
  rw [List.map_map]
  change x ∈ List.map id _ ↔ _
  rw [List.map_id, List.mem_filter]
  constructor
  · intro h; exact @of_decide_eq_true _ (Classical.propDecidable _) h.2
  · intro hx; exact ⟨mem_nodesUniv_of_history H hx, @decide_eq_true _ (Classical.propDecidable _) hx⟩

lemma decodeSet_tLabel_encodeHistory (n : ℕ) (H : History (Fin (n + 1))) (x : Node) :
    decodeSet (n + 1) (tLabel (encodeHistory n H) x) = H.val.label x := by
  unfold encodeHistory
  let dom := (nodesUniv n).filter (fun z =>
    @decide (z ∈ H.val.nodes) (Classical.propDecidable _))
  have hnodup : dom.Nodup := (nodesUniv_nodup n).filter _
  by_cases hx : x ∈ H.val.nodes
  · have hxdom : x ∈ dom := List.mem_filter.mpr
      ⟨mem_nodesUniv_of_history H hx, @decide_eq_true _ (Classical.propDecidable _) hx⟩
    rw [tLabel_map_of_mem hnodup _ hxdom, decodeSet_encodeSet]
  · have hxdom : x ∉ dom := fun hm =>
      hx (@of_decide_eq_true _ (Classical.propDecidable _) (List.mem_filter.mp hm).2)
    rw [tLabel_map_of_notMem _ hxdom, H.property.2.2.1 x hx]
    ext q; simp

lemma tLabel_encodeHistory_norm (n : ℕ) (H : History (Fin (n + 1))) (x : Node) :
    tLabel (encodeHistory n H) x = normalizeSet (n + 1) (tLabel (encodeHistory n H) x) := by
  unfold encodeHistory
  let dom := (nodesUniv n).filter (fun z =>
    @decide (z ∈ H.val.nodes) (Classical.propDecidable _))
  have hnodup : dom.Nodup := (nodesUniv_nodup n).filter _
  by_cases hx : x ∈ dom
  · rw [tLabel_map_of_mem hnodup _ hx, normalizeSet_encodeSet]
  · rw [tLabel_map_of_notMem _ hx]; simp [normalizeSet]

/-! #### Modular executable 5-stage functions (each small for instant `Primrec` checking) -/

def cDropLast (y : Node) : Node := y.reverse.tail.reverse
def cGetLast (y : Node) : ℕ := y.reverse.getD 0 0

lemma primrec_cDropLast : Primrec cDropLast :=
  Primrec.list_reverse.comp (Primrec.list_tail.comp Primrec.list_reverse)

lemma primrec_cGetLast : Primrec cGetLast :=
  (Primrec.list_getD 0).comp Primrec.list_reverse (Primrec.const 0)

lemma cDropLast_eq_dropLast (y : Node) : cDropLast y = y.dropLast := by
  induction y using List.reverseRecOn with
  | nil => rfl
  | append_singleton x i => rw [dropLast_concat]; simp [cDropLast]

lemma cGetLast_concat (x : Node) (i : ℕ) : cGetLast (x ++ [i]) = i := by
  simp [cGetLast]

lemma is_child_iff (x y : Node) :
    (cDropLast y = x ∧ y.length = x.length + 1) ↔ ∃ i, y = x ++ [i] := by
  constructor
  · rintro ⟨hd, hl⟩
    cases y using List.reverseRecOn with
    | nil => simp at hl
    | append_singleton z i =>
      rw [cDropLast_eq_dropLast, dropLast_concat] at hd
      subst hd
      exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    simp [cDropLast]

def cChildren (dom : List Node) (x : Node) : List Node :=
  dom.filter (fun y => decide (cDropLast y = x ∧ y.length = x.length + 1))

def cDegree (dom : List Node) (x : Node) : ℕ :=
  maxList ((cChildren dom x).map cGetLast)

lemma primrec₂_cChildren : Primrec₂ cChildren :=
  filter_primrec Primrec.fst
    ((Primrec.eq.comp (primrec_cDropLast.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)).and
      (Primrec.eq.comp (Primrec.list_length.comp Primrec.snd)
        (Primrec.succ.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst)))))

lemma primrec₂_cDegree : Primrec₂ cDegree :=
  primrec_maxList.comp (Primrec.list_map primrec₂_cChildren (primrec_cGetLast.comp Primrec.snd).to₂)

lemma mem_cChildren_iff (dom : List Node) (x y : Node) :
    y ∈ cChildren dom x ↔ y ∈ dom ∧ ∃ i, y = x ++ [i] := by
  simp [cChildren, is_child_iff]

lemma cDegree_eq_degree {dom : List Node} {T : Finset Node}
    (hdom : ∀ y, y ∈ dom ↔ y ∈ T) (x : Node) :
    cDegree dom x = degree T x := by
  apply le_antisymm
  · unfold cDegree; rw [maxList_eq_foldr_max]
    have hle : ∀ l : List ℕ, (∀ m ∈ l, m ≤ degree T x) → l.foldr max 0 ≤ degree T x := by
      intro l hl
      induction l with
      | nil => exact Nat.zero_le _
      | cons a as iha =>
        simp only [List.foldr_cons, max_le_iff]
        exact ⟨hl a List.mem_cons_self, iha (fun m hm => hl m (List.mem_cons_of_mem _ hm))⟩
    apply hle
    intro m hm
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
    obtain ⟨hydom, i, rfl⟩ := (mem_cChildren_iff dom x y).mp hy
    rw [cGetLast_concat]
    exact le_degree_of_mem ((hdom _).mp hydom)
  · unfold degree
    apply Finset.sup_le
    intro m hm
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hm
    simp only [children, Finset.mem_filter] at hy
    obtain ⟨hyT, i, rfl⟩ := hy
    rw [getLast!_concat]
    have hyc : x ++ [i] ∈ cChildren dom x :=
      (mem_cChildren_iff dom x _).mpr ⟨(hdom _).mpr hyT, i, rfl⟩
    exact le_maxList_of_mem (List.mem_map.mpr ⟨x ++ [i], hyc, cGetLast_concat x i⟩)

def cCompress (dom : List Node) (x : Node) : Node :=
  (List.range x.length).map (fun k =>
    ((List.range (x.getD k 0)).filter (fun j => decide (x.take k ++ [j] ∈ dom))).length + 1)

lemma primrec₂_cCompress : Primrec₂ cCompress := by
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd))
  have hdom : Primrec (fun p : (List Node × Node) × ℕ => p.1.1) := Primrec.fst.comp Primrec.fst
  have hx : Primrec (fun p : (List Node × Node) × ℕ => p.1.2) := Primrec.snd.comp Primrec.fst
  have hk : Primrec (fun p : (List Node × Node) × ℕ => p.2) := Primrec.snd
  have hbound : Primrec (fun p : (List Node × Node) × ℕ => p.1.2.getD p.2 0) :=
    (Primrec.list_getD 0).comp hx hk
  have hflt : Primrec (fun p : (List Node × Node) × ℕ =>
      (List.range (p.1.2.getD p.2 0)).filter (fun j => decide (p.1.2.take p.2 ++ [j] ∈ p.1.1))) :=
    filter_primrec (Primrec.list_range.comp hbound)
      (mem_list_primrec.comp
        (Primrec.list_append.comp (Primrec.list_take.comp (hk.comp Primrec.fst) (hx.comp Primrec.fst))
          (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))
        (hdom.comp Primrec.fst))
  exact (Primrec.succ.comp (Primrec.list_length.comp hflt)).to₂

lemma cCompress_eq_compress {dom : List Node} {T : Finset Node}
    (hdom : ∀ y, y ∈ dom ↔ y ∈ T) (x : Node) :
    cCompress dom x = compress T x := by
  unfold cCompress compress
  refine List.map_congr_left fun k hk => ?_
  have hlt : k < x.length := List.mem_range.mp hk
  have hget : x.getD k 0 = x[k]! := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
      List.getD_eq_getElem _ _ hlt]
  rw [hget]
  have hrk := childRank_eq_card_range T (x.take k) x[k]!
  unfold childRank at hrk
  rw [hrk]
  congr 1
  have hto : (((List.range x[k]!).filter (fun j => decide (x.take k ++ [j] ∈ dom))).toFinset) =
      (Finset.range x[k]!).filter (fun j => x.take k ++ [j] ∈ T) := by
    ext j; simp [hdom]
  rw [← hto, List.card_toFinset, List.dedup_eq_self.mpr (List.nodup_range.filter _)]

/-- One-step successor state set of node `x` in `c`. -/
def cNextLbl (A S a : ℕ) (trans : List (List ℕ)) (c : TreeCode) (x : Node) : List ℕ :=
  normalizeSet S ((tLabel c x).flatMap (fun q => trans.getD (A * q + a) []))

lemma cNextLbl_comp {X : Type} [Primcodable X]
    {A S a : X → ℕ} {trans : X → List (List ℕ)} {c : X → TreeCode} {x : X → Node}
    (hA : Primrec A) (hS : Primrec S) (ha : Primrec a) (hTrans : Primrec trans)
    (hc : Primrec c) (hx : Primrec x) :
    Primrec (fun w => cNextLbl (A w) (S w) (a w) (trans w) (c w) (x w)) := by
  refine normalizeSet_primrec.comp hS (Primrec.list_flatMap (primrec₂_tLabel.comp hc hx) ?_)
  exact ((Primrec.list_getD []).comp (hTrans.comp Primrec.fst)
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (hA.comp Primrec.fst) Primrec.snd)
      (ha.comp Primrec.fst))).to₂

/-- Stage 1 executable helper: `(dom1, pair1)` from `((αSize, B, a), c)`. -/
def cStage1 (ctx : ℕ × ListNBWCode × ℕ) (c : TreeCode) : List Node × TreeCode :=
  let A := ctx.1 + 1
  let B := ctx.2.1
  let a := ctx.2.2
  let S := B.1 + 1
  let ts := c.map Prod.fst
  let dom1 := dedupLeft (ts ++ ts.map (fun x => x ++ [cDegree ts x + 1]))
  let pair1 : TreeCode := dom1.map (fun y =>
    (y, if y ∈ ts then cNextLbl A S a B.2.2.1 c y
        else normalizeSet S ((cNextLbl A S a B.2.2.1 c (cDropLast y)).filter
          (fun q => decide (q ∈ B.2.2.2)))))
  (dom1, pair1)

lemma cStage1_comp {X : Type} [Primcodable X]
    {αSize : X → ℕ} {B : X → ListNBWCode} {a : X → ℕ} {c : X → TreeCode}
    (hα : Primrec αSize) (hB : Primrec B) (ha : Primrec a) (hc : Primrec c) :
    Primrec (fun w => cStage1 (αSize w, B w, a w) (c w)) := by
  have hA : Primrec (fun w => αSize w + 1) := Primrec.succ.comp hα
  have hS : Primrec (fun w => (B w).1 + 1) := Primrec.succ.comp (Primrec.fst.comp hB)
  have hTrans : Primrec (fun w => (B w).2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hB))
  have hAcc : Primrec (fun w => (B w).2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hB))
  have hts : Primrec (fun w => (c w).map Prod.fst) :=
    Primrec.list_map hc (Primrec.fst.comp Primrec.snd).to₂
  have hdom1 : Primrec (fun w =>
      dedupLeft ((c w).map Prod.fst ++
        ((c w).map Prod.fst).map (fun x => x ++ [cDegree ((c w).map Prod.fst) x + 1]))) :=
    dedupLeft_primrec.comp (Primrec.list_append.comp hts
      (Primrec.list_map hts
        (Primrec.list_append.comp Primrec.snd
          (Primrec.list_cons.comp
            (Primrec.succ.comp (primrec₂_cDegree.comp (hts.comp Primrec.fst) Primrec.snd))
            (Primrec.const []))).to₂))
  have hpair1 : Primrec (fun w => (cStage1 (αSize w, B w, a w) (c w)).2) := by
    have hOld := cNextLbl_comp (hA.comp Primrec.fst) (hS.comp Primrec.fst)
      (ha.comp Primrec.fst) (hTrans.comp Primrec.fst) (hc.comp Primrec.fst) Primrec.snd
    have hPar := cNextLbl_comp (hA.comp Primrec.fst) (hS.comp Primrec.fst)
      (ha.comp Primrec.fst) (hTrans.comp Primrec.fst) (hc.comp Primrec.fst)
      (primrec_cDropLast.comp Primrec.snd)
    have hLbl : Primrec (fun wy : X × Node =>
        if wy.2 ∈ (c wy.1).map Prod.fst then
          cNextLbl (αSize wy.1 + 1) ((B wy.1).1 + 1) (a wy.1) (B wy.1).2.2.1 (c wy.1) wy.2
        else
          normalizeSet ((B wy.1).1 + 1)
            ((cNextLbl (αSize wy.1 + 1) ((B wy.1).1 + 1) (a wy.1) (B wy.1).2.2.1 (c wy.1)
              (cDropLast wy.2)).filter (fun q => decide (q ∈ (B wy.1).2.2.2)))) :=
      Primrec.ite (mem_list_primrec.comp Primrec.snd (hts.comp Primrec.fst))
        hOld
        (normalizeSet_primrec.comp (hS.comp Primrec.fst)
          (filter_primrec hPar
            (mem_list_primrec.comp Primrec.snd (hAcc.comp (Primrec.fst.comp Primrec.fst)))))
    exact Primrec.list_map hdom1 (Primrec.snd.pair hLbl).to₂
  exact hdom1.pair hpair1

lemma cHasLeftJump_pred {X : Type} [Primcodable X]
    {dom1 : X → List Node} {pair1 : X → TreeCode} {x : X → Node} {q : X → ℕ}
    (hdom1 : Primrec dom1) (hpair1 : Primrec pair1) (hx : Primrec x) (hq : Primrec q) :
    PrimrecPred (fun w => ∃ m < (x w).length, ∃ j < (x w).getD m 0,
      0 < j ∧ ((x w).take m ++ [j]) ∈ dom1 w ∧
      q w ∈ tLabel (pair1 w) ((x w).take m ++ [j])) := by
  have hw : Primrec (fun u : (X × ℕ) × ℕ => u.1.1) := Primrec.fst.comp Primrec.fst
  have hm : Primrec (fun u : (X × ℕ) × ℕ => u.1.2) := Primrec.snd.comp Primrec.fst
  have hj : Primrec (fun u : (X × ℕ) × ℕ => u.2) := Primrec.snd
  have hcand : Primrec (fun u : (X × ℕ) × ℕ => (x u.1.1).take u.1.2 ++ [u.2]) :=
    Primrec.list_append.comp (Primrec.list_take.comp hm (hx.comp hw))
      (Primrec.list_cons.comp hj (Primrec.const []))
  have hInner := (Primrec.nat_lt.comp (Primrec.const 0) hj).and
    ((mem_list_primrec.comp hcand (hdom1.comp hw)).and
      (mem_list_primrec.comp (hq.comp hw) (primrec₂_tLabel.comp (hpair1.comp hw) hcand)))
  exact exists_lt_primrec (Primrec.list_length.comp hx)
    (exists_lt_primrec ((Primrec.list_getD 0).comp (hx.comp Primrec.fst) Primrec.snd) hInner)

/-- Stage 2 & 3 executable helper: `(dom3, pair3)` from `(dom1, pair1)`. -/
def cStage23 (s1 : List Node × TreeCode) : List Node × TreeCode :=
  let dom1 := s1.1
  let pair1 := s1.2
  let pair2 : TreeCode := dom1.map (fun x =>
    (x, (tLabel pair1 x).filter (fun q =>
      decide (¬ ∃ m < x.length, ∃ j < x.getD m 0,
        0 < j ∧ (x.take m ++ [j]) ∈ dom1 ∧ q ∈ tLabel pair1 (x.take m ++ [j])))))
  let dom3 := dom1.filter (fun x => decide (tLabel pair2 x ≠ []))
  (dom3, dom3.map (fun x => (x, tLabel pair2 x)))

lemma cStage23_comp {X : Type} [Primcodable X] {s1 : X → List Node × TreeCode}
    (hs1 : Primrec s1) : Primrec (fun w => cStage23 (s1 w)) := by
  have hdom1 := Primrec.fst.comp hs1
  have hpair1 := Primrec.snd.comp hs1
  have hpair2 := Primrec.list_map hdom1
    (Primrec.snd.pair
      (filter_primrec (primrec₂_tLabel.comp (hpair1.comp Primrec.fst) Primrec.snd)
        (cHasLeftJump_pred
          (hdom1.comp (Primrec.fst.comp Primrec.fst))
          (hpair1.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.snd.comp Primrec.fst) Primrec.snd).not)).to₂
  have hdom3 := filter_primrec hdom1
    (Primrec.eq.comp (primrec₂_tLabel.comp (hpair2.comp Primrec.fst) Primrec.snd)
      (Primrec.const ([] : List ℕ))).not
  exact hdom3.pair (Primrec.list_map hdom3
    (Primrec.snd.pair (primrec₂_tLabel.comp (hpair2.comp Primrec.fst) Primrec.snd)).to₂)

/-- Stage 4 executable helper: `(res3, dom4, pair4)` from `(S, (dom3, pair3))`. -/
def cStage4 (S : ℕ) (s3 : List Node × TreeCode) : List Node × List Node × TreeCode :=
  let dom3 := s3.1
  let pair3 := s3.2
  let res3 := dom3.filter (fun x =>
    decide (tLabel pair3 x = normalizeSet S ((cChildren dom3 x).flatMap (tLabel pair3))))
  let dom4 := dom3.filter (fun x => decide (¬ ∃ m < x.length, x.take m ∈ res3))
  (res3, dom4, dom4.map (fun x => (x, tLabel pair3 x)))

lemma cStage4_comp {X : Type} [Primcodable X]
    {S : X → ℕ} {s3 : X → List Node × TreeCode}
    (hS : Primrec S) (hs3 : Primrec s3) :
    Primrec (fun w => cStage4 (S w) (s3 w)) := by
  have hdom3 := Primrec.fst.comp hs3
  have hpair3 := Primrec.snd.comp hs3
  have hres3 := filter_primrec hdom3
    (Primrec.eq.comp (primrec₂_tLabel.comp (hpair3.comp Primrec.fst) Primrec.snd)
      (normalizeSet_primrec.comp (hS.comp Primrec.fst)
        (Primrec.list_flatMap (primrec₂_cChildren.comp (hdom3.comp Primrec.fst) Primrec.snd)
          (primrec₂_tLabel.comp (hpair3.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂)))
  have hdom4 := filter_primrec hdom3
    (exists_lt_primrec (Primrec.list_length.comp Primrec.snd)
      (mem_list_primrec.comp
        (Primrec.list_take.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
        (hres3.comp (Primrec.fst.comp Primrec.fst)))).not
  exact hres3.pair (hdom4.pair (Primrec.list_map hdom4
    (Primrec.snd.pair (primrec₂_tLabel.comp (hpair3.comp Primrec.fst) Primrec.snd)).to₂))

/-- Stage 5 executable helper: `(dom4, unst, acc, pair5)` from `((n, ts), (res3, dom4, pair4))`. -/
def cStage5 (nts : ℕ × List Node) (s4 : List Node × List Node × TreeCode) :
    List Node × List Node × List Node × TreeCode :=
  let n := nts.1
  let S := n + 1
  let ts := nts.2
  let res3 := s4.1
  let dom4 := s4.2.1
  let pair4 := s4.2.2
  let unst := ts.filter (fun x => decide (x ∉ dom4 ∨ cCompress dom4 x ≠ x))
  let acc := ts.filter (fun x => decide (x ∈ res3 ∧ x ∈ dom4 ∧ cCompress dom4 x = x))
  let dom5 := (nodesUniv n).filter (fun z => decide (∃ y ∈ dom4, cCompress dom4 y = z))
  let pair5 : TreeCode := dom5.map (fun z =>
    (z, normalizeSet S ((dom4.filter (fun y => decide (cCompress dom4 y = z))).flatMap (tLabel pair4))))
  (dom4, unst, acc, pair5)

lemma cStage5_comp {X : Type} [Primcodable X]
    {n : X → ℕ} {ts : X → List Node} {s4 : X → List Node × List Node × TreeCode}
    (hn : Primrec n) (hts : Primrec ts) (hs4 : Primrec s4) :
    Primrec (fun w => cStage5 (n w, ts w) (s4 w)) := by
  have hS := Primrec.succ.comp hn
  have hres3 := Primrec.fst.comp hs4
  have hdom4 := Primrec.fst.comp (Primrec.snd.comp hs4)
  have hpair4 := Primrec.snd.comp (Primrec.snd.comp hs4)
  have hunst := filter_primrec hts
    ((mem_list_primrec.comp Primrec.snd (hdom4.comp Primrec.fst)).not.or
      (Primrec.eq.comp (primrec₂_cCompress.comp (hdom4.comp Primrec.fst) Primrec.snd)
        Primrec.snd).not)
  have hacc := filter_primrec hts
    ((mem_list_primrec.comp Primrec.snd (hres3.comp Primrec.fst)).and
      ((mem_list_primrec.comp Primrec.snd (hdom4.comp Primrec.fst)).and
        (Primrec.eq.comp (primrec₂_cCompress.comp (hdom4.comp Primrec.fst) Primrec.snd)
          Primrec.snd)))
  have hdom5 := filter_primrec (primrec_nodesUniv.comp hn)
    (exists_mem_primrec (hdom4.comp Primrec.fst)
      (Primrec.eq.comp
        (primrec₂_cCompress.comp (hdom4.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
        (Primrec.snd.comp Primrec.fst)))
  have hpair5 := Primrec.list_map hdom5
    (Primrec.snd.pair
      (normalizeSet_primrec.comp (hS.comp Primrec.fst)
        (Primrec.list_flatMap
          (filter_primrec (hdom4.comp Primrec.fst)
            (Primrec.eq.comp
              (primrec₂_cCompress.comp (hdom4.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
              (Primrec.snd.comp Primrec.fst)))
          (primrec₂_tLabel.comp (hpair4.comp (Primrec.fst.comp Primrec.fst))
            Primrec.snd).to₂))).to₂
  exact hdom4.pair (hunst.pair (hacc.pair hpair5))

/-- Combined 5-stage executable transition `(dom4, unst, acc, pair5)`. -/
def cTreeTransitionData (αSize : ℕ) (B : ListNBWCode) (c : TreeCode) (a : ℕ) :
    List Node × List Node × List Node × TreeCode :=
  let s1 := cStage1 (αSize, B, a) c
  let s3 := cStage23 s1
  let s4 := cStage4 (B.1 + 1) s3
  cStage5 (B.1, c.map Prod.fst) s4

lemma cTreeTransitionData_comp {X : Type} [Primcodable X]
    {αSize : X → ℕ} {B : X → ListNBWCode} {c : X → TreeCode} {a : X → ℕ}
    (hα : Primrec αSize) (hB : Primrec B) (hc : Primrec c) (ha : Primrec a) :
    Primrec (fun w => cTreeTransitionData (αSize w) (B w) (c w) (a w)) := by
  have hn := Primrec.fst.comp hB
  have hts := Primrec.list_map hc (Primrec.fst.comp Primrec.snd).to₂
  have hs1 := cStage1_comp hα hB ha hc
  have hs3 := cStage23_comp hs1
  have hs4 := cStage4_comp (Primrec.succ.comp hn) hs3
  exact cStage5_comp hn hts hs4

def cTreeInit (B : ListNBWCode) : Option TreeCode :=
  let initNorm := normalizeSet (B.1 + 1) B.2.1
  if initNorm = [] then none else some [([], initNorm)]

lemma primrec_cTreeInit : Primrec cTreeInit := by
  have hnorm : Primrec (fun B : ListNBWCode => normalizeSet (B.1 + 1) B.2.1) :=
    normalizeSet_primrec.comp (Primrec.succ.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  exact Primrec.ite (Primrec.eq.comp hnorm (Primrec.const ([] : List ℕ)))
    (Primrec.const (none : Option TreeCode))
    (Primrec.option_some.comp
      (Primrec.list_cons.comp ((Primrec.const ([] : Node)).pair hnorm) (Primrec.const [])))

/-! #### Modular stage-by-stage semantic correspondence proofs -/

lemma cTreeInit_eq_encode (αSize : ℕ) (B : ListNBWCode) :
    cTreeInit B = (initialHistory (toSemNBW αSize B)).map (encodeHistory B.1) := by
  let Bsem := toSemNBW αSize B
  unfold cTreeInit
  by_cases hemp : normalizeSet (B.1 + 1) B.2.1 = []
  · rw [if_pos hemp]
    have hinit_empty : Bsem.initial = ∅ := (normalizeSet_eq_nil_iff (B.1 + 1) B.2.1).mp hemp
    have hnotv : ¬ Valid (initialData Bsem) := by rw [valid_initialData_iff, hinit_empty]; simp
    unfold initialHistory asHistory
    rw [dif_neg hnotv]; rfl
  · rw [if_neg hemp]
    have hinit_ne : Bsem.initial.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro he; exact hemp ((normalizeSet_eq_nil_iff (B.1 + 1) B.2.1).mpr he)
    obtain ⟨H0, hinit, hH0⟩ := initialHistory_of_nonempty Bsem hinit_ne
    rw [hinit, Option.map_some]
    congr 1
    unfold encodeHistory
    have hdom : (nodesUniv B.1).filter
        (fun x => @decide (x ∈ H0.val.nodes) (Classical.propDecidable _)) = [[]] := by
      obtain ⟨rest, hhead⟩ := dedupLeft_cons_head ([] : Node)
        ((List.range (B.1 + 1)).flatMap (fun len => wordsOf ((List.range (B.1 + 1)).map (· + 1)) len))
      have hnodup := nodesUniv_nodup B.1
      unfold nodesUniv at hnodup ⊢
      rw [hhead] at hnodup ⊢
      obtain ⟨hnil_not, _⟩ := List.nodup_cons.mp hnodup
      rw [List.filter_cons_of_pos (by
        rw [@decide_eq_true_iff _ (Classical.propDecidable _), hH0]; simp [initialData])]
      congr 1
      rw [List.filter_eq_nil_iff]
      intro y hy hdec
      have hy0 : y ∈ H0.val.nodes := @of_decide_eq_true _ (Classical.propDecidable _) hdec
      rw [hH0] at hy0
      simp only [initialData, Finset.mem_singleton] at hy0
      exact hnil_not (hy0 ▸ hy)
    rw [hdom, List.map_singleton]
    congr 2
    rw [hH0]
    simp only [initialData, ↓reduceIte]
    rw [← normalizeSet_encodeSet Bsem.initial, normalizeSet_eq_iff, decodeSet_encodeSet]
    rfl

lemma exists_split_iff_lt_length (x : Node) (P : Node → ℕ → Prop) :
    (∃ p i v, x = p ++ i :: v ∧ P p i) ↔
      ∃ m < x.length, P (x.take m) (x.getD m 0) := by
  constructor
  · rintro ⟨p, i, v, rfl, hp⟩
    refine ⟨p.length, by simp, ?_⟩
    have htk : (p ++ i :: v).take p.length = p := List.take_left
    have hgd : (p ++ i :: v).getD p.length 0 = i := by
      have hlt : p.length < (p ++ i :: v).length := by simp
      rw [List.getD_eq_getElem _ _ hlt, List.getElem_append_right le_rfl]; simp
    rwa [htk, hgd]
  · rintro ⟨m, hm, hp⟩
    refine ⟨x.take m, x.getD m 0, x.drop (m + 1), ?_, hp⟩
    rw [List.getD_eq_getElem _ _ hm]
    conv_lhs => rw [← List.take_append_drop m x, List.drop_eq_getElem_cons hm]

lemma exists_proper_prefix_iff_lt_length (x : Node) (P : Node → Prop) :
    (∃ p, P p ∧ p.IsPrefix x ∧ p ≠ x) ↔ ∃ m < x.length, P (x.take m) := by
  constructor
  · rintro ⟨p, hp, hpre, hne⟩
    have hlt : p.length < x.length :=
      lt_of_le_of_ne hpre.length_le (fun hl => hne (eq_of_prefix_of_length_eq hpre hl))
    obtain ⟨t, rfl⟩ := hpre
    exact ⟨p.length, hlt, by simpa [List.take_left] using hp⟩
  · rintro ⟨m, hm, hp⟩
    refine ⟨x.take m, hp, List.take_prefix m x, ?_⟩
    intro heq
    have hl := congrArg List.length heq
    rw [List.length_take_of_le (Nat.le_of_lt hm)] at hl; omega

lemma cStage1_spec (αSize : ℕ) (B : ListNBWCode) (H : History (Fin (B.1 + 1)))
    (a : Fin (αSize + 1)) :
    (cStage1 (αSize, B, a.val) (encodeHistory B.1 H)).1.Nodup ∧
    (∀ y, y ∈ (cStage1 (αSize, B, a.val) (encodeHistory B.1 H)).1 ↔
      y ∈ (expand (toSemNBW αSize B) H.val a).nodes) ∧
    (∀ y, decodeSet (B.1 + 1) (tLabel (cStage1 (αSize, B, a.val) (encodeHistory B.1 H)).2 y) =
      (expand (toSemNBW αSize B) H.val a).label y) ∧
    (∀ y, tLabel (cStage1 (αSize, B, a.val) (encodeHistory B.1 H)).2 y =
      normalizeSet (B.1 + 1) (tLabel (cStage1 (αSize, B, a.val) (encodeHistory B.1 H)).2 y)) := by
  have hts_mem : ∀ y, y ∈ (encodeHistory B.1 H).map Prod.fst ↔ y ∈ H.val.nodes :=
    encodeHistory_fst_mem_iff B.1 H
  have hc_lbl : ∀ y, decodeSet (B.1 + 1) (tLabel (encodeHistory B.1 H) y) = H.val.label y :=
    decodeSet_tLabel_encodeHistory B.1 H
  have hc_norm : ∀ y, tLabel (encodeHistory B.1 H) y =
      normalizeSet (B.1 + 1) (tLabel (encodeHistory B.1 H) y) :=
    tLabel_encodeHistory_norm B.1 H
  have hnextLbl_mem : ∀ x (q : Fin (B.1 + 1)),
      q.val ∈ cNextLbl (αSize + 1) (B.1 + 1) a.val B.2.2.1 (encodeHistory B.1 H) x ↔
        ∃ r ∈ H.val.label x, q ∈ (toSemNBW αSize B).delta r a := by
    intro x q
    simp only [cNextLbl, mem_normalizeSet, q.isLt, true_and, List.mem_flatMap, toSemNBW,
      mem_decodeSet]
    constructor
    · rintro ⟨r, hr, htr⟩
      have hrl : r < B.1 + 1 := by
        have hr' := hr; rw [hc_norm x, mem_normalizeSet] at hr'; exact hr'.1
      have hrmem : (⟨r, hrl⟩ : Fin (B.1 + 1)) ∈ H.val.label x := by
        rw [← hc_lbl x, mem_decodeSet]; exact hr
      exact ⟨⟨r, hrl⟩, hrmem, htr⟩
    · rintro ⟨r, hrmem, htr⟩
      rw [← hc_lbl x, mem_decodeSet] at hrmem
      exact ⟨r.val, hrmem, htr⟩
  let ts := (encodeHistory B.1 H).map Prod.fst
  let dom1 := dedupLeft (ts ++ ts.map (fun x => x ++ [cDegree ts x + 1]))
  have hdeg : ∀ x, cDegree ts x = degree H.val.nodes x := cDegree_eq_degree hts_mem
  have hdom1_nodup : dom1.Nodup := nodup_dedupLeft _
  have hdom1_mem : ∀ y, y ∈ dom1 ↔ y ∈ (expand (toSemNBW αSize B) H.val a).nodes := by
    intro y
    simp only [dom1, ts, mem_dedupLeft, List.mem_append, List.mem_map, hts_mem, hdeg,
      expand_mem_iff]
    apply or_congr_right
    constructor
    · rintro ⟨x, hx, h⟩; exact ⟨x, hx, h.symm⟩
    · rintro ⟨x, hx, h⟩; exact ⟨x, hx, h.symm⟩
  let pair1 : TreeCode := dom1.map (fun y =>
    (y, if y ∈ ts then cNextLbl (αSize + 1) (B.1 + 1) a.val B.2.2.1 (encodeHistory B.1 H) y
        else normalizeSet (B.1 + 1)
          ((cNextLbl (αSize + 1) (B.1 + 1) a.val B.2.2.1 (encodeHistory B.1 H) (cDropLast y)).filter
            (fun q => decide (q ∈ B.2.2.2)))))
  have hs1_eq : cStage1 (αSize, B, a.val) (encodeHistory B.1 H) = (dom1, pair1) := rfl
  rw [hs1_eq]
  refine ⟨hdom1_nodup, hdom1_mem, ?_, ?_⟩
  · intro y
    dsimp only
    by_cases hy1 : y ∈ dom1
    · rw [tLabel_map_of_mem hdom1_nodup _ hy1]
      by_cases hy0 : y ∈ ts
      · rw [if_pos hy0, expand_label_old (toSemNBW αSize B) H.val a ((hts_mem y).mp hy0)]
        ext q
        simp only [mem_decodeSet, Finset.mem_biUnion, hnextLbl_mem]
      · rw [if_neg hy0]
        have hy0' : y ∉ H.val.nodes := fun hm => hy0 ((hts_mem y).mpr hm)
        rcases (expand_mem_iff (toSemNBW αSize B) H.val a y).mp ((hdom1_mem y).mp hy1) with
          hfalse | ⟨x, hx, rfl⟩
        · exact absurd hfalse hy0'
        · rw [cDropLast_eq_dropLast, dropLast_concat,
            expand_label_new (toSemNBW αSize B) H.val a hx, decodeSet_normalizeSet]
          ext q
          simp only [mem_decodeSet, List.mem_filter, decide_eq_true_eq, Finset.mem_inter,
            Finset.mem_biUnion, hnextLbl_mem, toSemNBW]
    · rw [tLabel_map_of_notMem _ hy1]
      have hy_not : y ∉ (expand (toSemNBW αSize B) H.val a).nodes :=
        fun hm => hy1 ((hdom1_mem y).mpr hm)
      rw [expand_label_outside (toSemNBW αSize B) H.val a hy_not]
      ext q; simp
  · intro y
    dsimp only
    by_cases hy1 : y ∈ dom1
    · rw [tLabel_map_of_mem hdom1_nodup _ hy1]
      split_ifs <;> simp [cNextLbl, normalizeSet_idem]
    · rw [tLabel_map_of_notMem _ hy1]; simp [normalizeSet]

lemma cStage23_spec {S αSize : ℕ} {Bsem : SemNBW (Fin S) (Fin (αSize + 1))}
    {H : TreeData (Fin S)} {a : Fin (αSize + 1)} {s1 : List Node × TreeCode}
    (h1_nodup : s1.1.Nodup)
    (h1_mem : ∀ y, y ∈ s1.1 ↔ y ∈ (expand Bsem H a).nodes)
    (h1_dec : ∀ y, decodeSet S (tLabel s1.2 y) = (expand Bsem H a).label y)
    (h1_norm : ∀ y, tLabel s1.2 y = normalizeSet S (tLabel s1.2 y)) :
    (cStage23 s1).1.Nodup ∧
    (∀ x, x ∈ (cStage23 s1).1 ↔ x ∈ (stage3 Bsem H a).nodes) ∧
    (∀ x, decodeSet S (tLabel (cStage23 s1).2 x) = (stage3 Bsem H a).label x) ∧
    (∀ x, tLabel (cStage23 s1).2 x = normalizeSet S (tLabel (cStage23 s1).2 x)) := by
  rcases s1 with ⟨dom1, pair1⟩
  dsimp only at *
  let pair2 : TreeCode := dom1.map (fun x =>
    (x, (tLabel pair1 x).filter (fun q =>
      decide (¬ ∃ m < x.length, ∃ j < x.getD m 0,
        0 < j ∧ (x.take m ++ [j]) ∈ dom1 ∧ q ∈ tLabel pair1 (x.take m ++ [j])))))
  have hpair2_dec : ∀ x, decodeSet S (tLabel pair2 x) =
      (horizontal (expand Bsem H a)).label x := by
    intro x
    by_cases hx1 : x ∈ dom1
    · rw [tLabel_map_of_mem h1_nodup _ hx1]
      ext q
      rw [mem_decodeSet, List.mem_filter, decide_eq_true_eq, mem_horizontal_label_iff,
        ← h1_dec x, mem_decodeSet]
      refine and_congr_right fun _ => not_congr ?_
      have heq := exists_split_iff_lt_length x (fun p i =>
        ∃ j, 0 < j ∧ j < i ∧ p ++ [j] ∈ dom1 ∧ q.val ∈ tLabel pair1 (p ++ [j]))
      constructor
      · rintro ⟨m, hm, j, hjlt, hj0, hm1, hm2⟩
        obtain ⟨p, i, v, hsplit, j', hj'0, hj'lt, h1', h2'⟩ :=
          heq.mpr ⟨m, hm, j, hj0, hjlt, hm1, hm2⟩
        exact ⟨p, i, v, j', hsplit, hj'0, hj'lt, (h1_mem _).mp h1',
          by rwa [← h1_dec _, mem_decodeSet]⟩
      · rintro ⟨p, i, v, j, hsplit, hj0, hjlt, hm1, hm2⟩
        obtain ⟨m, hm, j', hj'0, hj'lt, h1', h2'⟩ :=
          heq.mp ⟨p, i, v, hsplit, j, hj0, hjlt, (h1_mem _).mpr hm1,
            by rwa [← mem_decodeSet, h1_dec _]⟩
        exact ⟨m, hm, j', hj'lt, hj'0, h1', h2'⟩
    · rw [tLabel_map_of_notMem _ hx1]
      have hx_not : x ∉ (expand Bsem H a).nodes := fun hm => hx1 ((h1_mem x).mpr hm)
      ext q
      rw [mem_decodeSet, mem_horizontal_label_iff, expand_label_outside Bsem H a hx_not]
      simp
  have hpair2_norm : ∀ x, tLabel pair2 x = normalizeSet S (tLabel pair2 x) := by
    intro x
    by_cases hx1 : x ∈ dom1
    · rw [tLabel_map_of_mem h1_nodup _ hx1, h1_norm x]
      simp only [normalizeSet, List.filter_filter]
      apply List.filter_congr
      intro q hq
      simp only [List.mem_filter, List.mem_range]
      have hql : q < S := List.mem_range.mp hq
      simp [hql]
    · rw [tLabel_map_of_notMem _ hx1]; simp [normalizeSet]
  let dom3 := dom1.filter (fun x => decide (tLabel pair2 x ≠ []))
  have hdom3_nodup : dom3.Nodup := h1_nodup.filter _
  have hdom3_mem : ∀ x, x ∈ dom3 ↔ x ∈ (stage3 Bsem H a).nodes := by
    intro x
    rw [List.mem_filter, decide_eq_true_eq, stage3_mem_iff, h1_mem, Finset.nonempty_iff_ne_empty,
      ← hpair2_dec, ne_eq, ne_eq, ← normalizeSet_eq_nil_iff, ← hpair2_norm]
  let pair3 : TreeCode := dom3.map (fun x => (x, tLabel pair2 x))
  have hs3_eq : cStage23 (dom1, pair1) = (dom3, pair3) := rfl
  rw [hs3_eq]
  refine ⟨hdom3_nodup, hdom3_mem, ?_, ?_⟩
  · intro x
    dsimp only
    by_cases hx3 : x ∈ dom3
    · rw [tLabel_map_of_mem hdom3_nodup _ hx3, hpair2_dec,
        stage3_label_of_mem Bsem H a ((hdom3_mem x).mp hx3)]
    · rw [tLabel_map_of_notMem _ hx3]
      have hx3' : x ∉ (stage3 Bsem H a).nodes := fun hm => hx3 ((hdom3_mem x).mpr hm)
      change decodeSet S [] = if x ∈ (stage3 Bsem H a).nodes then _ else ∅
      rw [if_neg hx3']; ext q; simp
  · intro x
    dsimp only
    by_cases hx3 : x ∈ dom3
    · rw [tLabel_map_of_mem hdom3_nodup _ hx3]; exact hpair2_norm x
    · rw [tLabel_map_of_notMem _ hx3]; simp [normalizeSet]

lemma cStage4_spec {S αSize : ℕ} {Bsem : SemNBW (Fin S) (Fin (αSize + 1))}
    {H : TreeData (Fin S)} {a : Fin (αSize + 1)} {s3 : List Node × TreeCode}
    (h3_nodup : s3.1.Nodup)
    (h3_mem : ∀ x, x ∈ s3.1 ↔ x ∈ (stage3 Bsem H a).nodes)
    (h3_dec : ∀ x, decodeSet S (tLabel s3.2 x) = (stage3 Bsem H a).label x)
    (h3_norm : ∀ x, tLabel s3.2 x = normalizeSet S (tLabel s3.2 x)) :
    (cStage4 S s3).2.1.Nodup ∧
    (∀ x, x ∈ (cStage4 S s3).1 ↔ x ∈ resetNodes (stage3 Bsem H a)) ∧
    (∀ x, x ∈ (cStage4 S s3).2.1 ↔ x ∈ (stage4 Bsem H a).nodes) ∧
    (∀ x, decodeSet S (tLabel (cStage4 S s3).2.2 x) = (stage4 Bsem H a).label x) := by
  rcases s3 with ⟨dom3, pair3⟩
  dsimp only at *
  let res3 := dom3.filter (fun x =>
    decide (tLabel pair3 x = normalizeSet S ((cChildren dom3 x).flatMap (tLabel pair3))))
  have hres3_mem : ∀ x, x ∈ res3 ↔ x ∈ resetNodes (stage3 Bsem H a) := by
    intro x
    rw [List.mem_filter, decide_eq_true_eq, h3_mem]
    simp only [resetNodes, Finset.mem_filter]
    refine and_congr_right fun _ => ?_
    have hlhs : (tLabel pair3 x = normalizeSet S ((cChildren dom3 x).flatMap (tLabel pair3))) ↔
        decodeSet S (tLabel pair3 x) =
          decodeSet S ((cChildren dom3 x).flatMap (tLabel pair3)) := by
      conv_lhs => rw [h3_norm x]
      rw [normalizeSet_eq_iff]
    rw [hlhs, h3_dec x]
    suffices hch : decodeSet S ((cChildren dom3 x).flatMap (tLabel pair3)) =
        childLabels (stage3 Bsem H a) x by rw [hch]
    ext q
    simp only [mem_decodeSet, List.mem_flatMap, childLabels, Finset.mem_biUnion, children,
      Finset.mem_filter, mem_cChildren_iff, h3_mem]
    constructor
    · rintro ⟨y, ⟨hy3, hi⟩, hqy⟩
      exact ⟨y, ⟨hy3, hi⟩, by rwa [← h3_dec y, mem_decodeSet]⟩
    · rintro ⟨y, ⟨hy3, hi⟩, hqy⟩
      exact ⟨y, ⟨hy3, hi⟩, by rwa [← mem_decodeSet, h3_dec y]⟩
  let dom4 := dom3.filter (fun x => decide (¬ ∃ m < x.length, x.take m ∈ res3))
  have hdom4_nodup : dom4.Nodup := h3_nodup.filter _
  have hdom4_mem : ∀ x, x ∈ dom4 ↔ x ∈ (stage4 Bsem H a).nodes := by
    intro x
    rw [List.mem_filter, decide_eq_true_eq, stage4_mem_iff, h3_mem]
    refine and_congr_right fun _ => not_congr ?_
    rw [← exists_proper_prefix_iff_lt_length x (fun p => p ∈ res3)]
    simp only [hres3_mem]
  let pair4 : TreeCode := dom4.map (fun x => (x, tLabel pair3 x))
  have hs4_eq : cStage4 S (dom3, pair3) = (res3, dom4, pair4) := rfl
  rw [hs4_eq]
  refine ⟨hdom4_nodup, hres3_mem, hdom4_mem, ?_⟩
  intro x
  dsimp only
  by_cases hx4 : x ∈ dom4
  · rw [tLabel_map_of_mem hdom4_nodup _ hx4, h3_dec,
      stage4_label_of_mem Bsem H a ((hdom4_mem x).mp hx4)]
  · rw [tLabel_map_of_notMem _ hx4]
    have hx4' : x ∉ (stage4 Bsem H a).nodes := fun hm => hx4 ((hdom4_mem x).mpr hm)
    change decodeSet S [] = if x ∈ (stage4 Bsem H a).nodes then _ else ∅
    rw [if_neg hx4']; ext q; simp

lemma cStage5_spec {n αSize : ℕ} {Bsem : SemNBW (Fin (n + 1)) (Fin (αSize + 1))}
    {H : History (Fin (n + 1))} {a : Fin (αSize + 1)} {ts : List Node}
    {s4 : List Node × List Node × TreeCode}
    (hts_mem : ∀ y, y ∈ ts ↔ y ∈ H.val.nodes)
    (hres3_mem : ∀ x, x ∈ s4.1 ↔ x ∈ resetNodes (stage3 Bsem H.val a))
    (hdom4_mem : ∀ x, x ∈ s4.2.1 ↔ x ∈ (stage4 Bsem H.val a).nodes)
    (hpair4_dec : ∀ x, decodeSet (n + 1) (tLabel s4.2.2 x) = (stage4 Bsem H.val a).label x) :
    (∀ y, y ∈ (cStage5 (n, ts) s4).1 ↔ y ∈ (stage4 Bsem H.val a).nodes) ∧
    (∀ y, y ∈ (cStage5 (n, ts) s4).2.1 ↔ y ∈ unstable Bsem H a) ∧
    (∀ y, y ∈ (cStage5 (n, ts) s4).2.2.1 ↔ y ∈ acceptingNodes Bsem H a) ∧
    ((if ([] : Node) ∈ (cStage5 (n, ts) s4).1 then some (cStage5 (n, ts) s4).2.2.2 else none) =
      (successor Bsem H a).map (encodeHistory n)) := by
  rcases s4 with ⟨res3, dom4, pair4⟩
  dsimp only at *
  have hcomp4 : ∀ x, cCompress dom4 x = compress (stage4 Bsem H.val a).nodes x :=
    cCompress_eq_compress hdom4_mem
  let unst := ts.filter (fun x => decide (x ∉ dom4 ∨ cCompress dom4 x ≠ x))
  have hunst_mem : ∀ x, x ∈ unst ↔ x ∈ unstable Bsem H a := by
    intro x
    rw [List.mem_filter, decide_eq_true_eq]
    simp only [unstable, Finset.mem_filter, hts_mem, hdom4_mem, hcomp4]
  let acc := ts.filter (fun x => decide (x ∈ res3 ∧ x ∈ dom4 ∧ cCompress dom4 x = x))
  have hacc_mem : ∀ x, x ∈ acc ↔ x ∈ acceptingNodes Bsem H a := by
    intro x
    rw [List.mem_filter, decide_eq_true_eq]
    simp only [acceptingNodes, Finset.mem_filter, hts_mem, hres3_mem, hdom4_mem, hcomp4]
  let dom5 := (nodesUniv n).filter (fun z => decide (∃ y ∈ dom4, cCompress dom4 y = z))
  let pair5 : TreeCode := dom5.map (fun z =>
    (z, normalizeSet (n + 1) ((dom4.filter (fun y => decide (cCompress dom4 y = z))).flatMap
      (tLabel pair4))))
  have hres_eq : cStage5 (n, ts) (res3, dom4, pair4) = (dom4, unst, acc, pair5) := rfl
  rw [hres_eq]
  refine ⟨hdom4_mem, hunst_mem, hacc_mem, ?_⟩
  dsimp only
  by_cases hroot4 : ([] : Node) ∈ dom4
  · rw [if_pos hroot4]
    have hroot_sem : ([] : Node) ∈ (stage4 Bsem H.val a).nodes := (hdom4_mem []).mp hroot4
    have hv' := stage4_valid_compressed Bsem H a hroot_sem
    let H' : History (Fin (n + 1)) := ⟨compressed (stage4 Bsem H.val a), hv'⟩
    have hsucc : successor Bsem H a = some H' := (successor_eq_some_iff Bsem H a H').mpr rfl
    rw [hsucc, Option.map_some, Option.some.injEq]
    unfold encodeHistory
    have hdom5_eq : dom5 = (nodesUniv n).filter
        (fun z => @decide (z ∈ H'.val.nodes) (Classical.propDecidable _)) := by
      apply List.filter_congr
      intro z _
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq, @decide_eq_true_iff _ (Classical.propDecidable _)]
      change (∃ y ∈ dom4, cCompress dom4 y = z) ↔ z ∈ (compressed (stage4 Bsem H.val a)).nodes
      simp only [compressed, Finset.mem_image, hdom4_mem, hcomp4]
    dsimp only [pair5]
    rw [hdom5_eq]
    apply List.map_congr_left
    intro z _
    congr 1
    rw [← normalizeSet_encodeSet (H'.val.label z), normalizeSet_eq_iff, decodeSet_encodeSet]
    ext q
    change q ∈ decodeSet (n + 1) _ ↔ q ∈ (compressed (stage4 Bsem H.val a)).label z
    simp only [compressed, mem_decodeSet, List.mem_flatMap, List.mem_filter, decide_eq_true_eq,
      Finset.mem_biUnion, Finset.mem_filter, hdom4_mem, hcomp4]
    constructor
    · rintro ⟨y, ⟨hy4, hyz⟩, hqy⟩
      exact ⟨y, ⟨hy4, hyz⟩, by rwa [← hpair4_dec y, mem_decodeSet]⟩
    · rintro ⟨y, ⟨hy4, hyz⟩, hqy⟩
      exact ⟨y, ⟨hy4, hyz⟩, by rwa [← mem_decodeSet, hpair4_dec y]⟩
  · rw [if_neg hroot4]
    have hroot_not : ([] : Node) ∉ (stage4 Bsem H.val a).nodes :=
      fun hm => hroot4 ((hdom4_mem []).mpr hm)
    cases hsucc : successor Bsem H a with
    | none => rfl
    | some H' => exact absurd (root_mem_stage4_of_succ Bsem hsucc) hroot_not

lemma cTreeTransitionData_spec (αSize : ℕ) (B : ListNBWCode)
    (H : History (Fin (B.1 + 1))) (a : Fin (αSize + 1)) :
    (∀ y, y ∈ (cTreeTransitionData αSize B (encodeHistory B.1 H) a.val).1 ↔
      y ∈ (stage4 (toSemNBW αSize B) H.val a).nodes) ∧
    (∀ y, y ∈ (cTreeTransitionData αSize B (encodeHistory B.1 H) a.val).2.1 ↔
      y ∈ unstable (toSemNBW αSize B) H a) ∧
    (∀ y, y ∈ (cTreeTransitionData αSize B (encodeHistory B.1 H) a.val).2.2.1 ↔
      y ∈ acceptingNodes (toSemNBW αSize B) H a) ∧
    ((if ([] : Node) ∈ (cTreeTransitionData αSize B (encodeHistory B.1 H) a.val).1 then
        some (cTreeTransitionData αSize B (encodeHistory B.1 H) a.val).2.2.2 else none) =
      (successor (toSemNBW αSize B) H a).map (encodeHistory B.1)) := by
  unfold cTreeTransitionData
  dsimp only
  obtain ⟨h1_nodup, h1_mem, h1_dec, h1_norm⟩ := cStage1_spec αSize B H a
  obtain ⟨h3_nodup, h3_mem, h3_dec, h3_norm⟩ := cStage23_spec h1_nodup h1_mem h1_dec h1_norm
  obtain ⟨_, hres3_mem, hdom4_mem, hpair4_dec⟩ := cStage4_spec h3_nodup h3_mem h3_dec h3_norm
  exact cStage5_spec (encodeHistory_fst_mem_iff B.1 H) hres3_mem hdom4_mem hpair4_dec

/-! #### Index Appearance Record (IAR) from Transition-Rabin to DPA -/

lemma perm_filter_not_append_filter {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.filter (fun x => !p x) ++ l.filter p).Perm l
  | [] => List.Perm.nil
  | x :: xs => by
    cases hx : p x
    · simp only [List.filter_cons, hx, Bool.not_false, ↓reduceIte, List.cons_append]
      exact List.Perm.cons x (perm_filter_not_append_filter p xs)
    · simp only [List.filter_cons, hx, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact List.perm_middle.trans ((perm_filter_not_append_filter p xs).cons x)

lemma decide_not_eq (p : Prop) [Decidable p] : decide (¬ p) = !decide p := by
  cases ‹Decidable p› <;> rfl

abbrev IARCode : Type := Option (TreeCode × List ℕ × ℕ)

def cIARInit (B : ListNBWCode) : IARCode :=
  let k := (nodesUniv B.1).length
  match cTreeInit B with
  | none => none
  | some c0 => some (c0, List.range k, 2 * k + 1)

def cIARPrio (n : ℕ) (s : IARCode) : ℕ :=
  let k := (nodesUniv n).length
  match s with
  | none => 2 * k + 1
  | some (_, _, p) => p

def cIARBuildFromRes (univ : List Node) (perm : List ℕ)
    (res : List Node × List Node × List Node × TreeCode) : IARCode :=
  let k := univ.length
  let dom4 := res.1
  let unst := res.2.1
  let acc := res.2.2.1
  let nextC := res.2.2.2
  if ([] : Node) ∈ dom4 then
    let isU : ℕ → Bool := fun i => decide (univ.getD i [] ∈ unst)
    let isG : ℕ → Bool := fun i => decide (univ.getD i [] ∈ acc)
    let uPrios := ((List.range k).filter isU).map (fun i => 2 * cIdxOf perm i + 1)
    let gPrios := ((List.range k).filter isG).map (fun i => 2 * cIdxOf perm i + 2)
    let p' := minWith (2 * k + 1) (uPrios ++ gPrios)
    let perm' := perm.filter (fun i => !isU i) ++ perm.filter isU
    some (nextC, perm', p')
  else
    none

lemma cIARBuildFromRes_comp {X : Type} [Primcodable X]
    {univ : X → List Node} {perm : X → List ℕ}
    {res : X → List Node × List Node × List Node × TreeCode}
    (hUniv : Primrec univ) (hPerm : Primrec perm) (hRes : Primrec res) :
    Primrec (fun w => cIARBuildFromRes (univ w) (perm w) (res w)) := by
  have hDom4 := Primrec.fst.comp hRes
  have hUnst := Primrec.fst.comp (Primrec.snd.comp hRes)
  have hAcc := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hRes))
  have hNext := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hRes))
  have hK := Primrec.list_length.comp hUniv
  have hIsU : PrimrecPred (fun wi : X × ℕ => (univ wi.1).getD wi.2 [] ∈ (res wi.1).2.1) :=
    mem_list_primrec.comp ((Primrec.list_getD []).comp (hUniv.comp Primrec.fst) Primrec.snd)
      (hUnst.comp Primrec.fst)
  have hIsG : PrimrecPred (fun wi : X × ℕ => (univ wi.1).getD wi.2 [] ∈ (res wi.1).2.2.1) :=
    mem_list_primrec.comp ((Primrec.list_getD []).comp (hUniv.comp Primrec.fst) Primrec.snd)
      (hAcc.comp Primrec.fst)
  have huIdx := filter_primrec (Primrec.list_range.comp hK) hIsU
  have hgIdx := filter_primrec (Primrec.list_range.comp hK) hIsG
  have huPrios := Primrec.list_map huIdx
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (cIdxOf_primrec.comp (hPerm.comp Primrec.fst) Primrec.snd))).to₂
  have hgPrios := Primrec.list_map hgIdx
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (cIdxOf_primrec.comp (hPerm.comp Primrec.fst) Primrec.snd)) (Primrec.const 2)).to₂
  have hp' := primrec₂_minWith.comp
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) hK))
    (Primrec.list_append.comp huPrios hgPrios)
  have hperm' := Primrec.list_append.comp
    (filter_primrec hPerm hIsU.not) (filter_primrec hPerm hIsU)
  exact (Primrec.ite (mem_list_primrec.comp (Primrec.const ([] : Node)) hDom4)
    (Primrec.option_some.comp (hNext.pair (hperm'.pair hp')))
    (Primrec.const (none : IARCode))).of_eq fun w => by
      simp only [cIARBuildFromRes, decide_not_eq]

def cIARStep (αSize : ℕ) (B : ListNBWCode) (s : IARCode) (a : ℕ) : IARCode :=
  match s with
  | none => none
  | some (c, perm, _) =>
    cIARBuildFromRes (nodesUniv B.1) perm (cTreeTransitionData αSize B c a)

lemma primrec_cIARInit : Primrec cIARInit := by
  have hk : Primrec (fun B : ListNBWCode => (nodesUniv B.1).length) :=
    Primrec.list_length.comp (primrec_nodesUniv.comp Primrec.fst)
  have hp : Primrec (fun B : ListNBWCode => 2 * (nodesUniv B.1).length + 1) :=
    Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) hk)
  exact (Primrec.option_casesOn primrec_cTreeInit (Primrec.const (none : IARCode))
    (Primrec.option_some.comp
      (Primrec.snd.pair
        ((Primrec.list_range.comp (hk.comp Primrec.fst)).pair (hp.comp Primrec.fst)))).to₂).of_eq
    (fun B => by simp only [cIARInit]; cases cTreeInit B <;> rfl)

lemma primrec₂_cIARPrio : Primrec₂ cIARPrio := by
  have hdef : Primrec (fun p : ℕ × IARCode => 2 * (nodesUniv p.1).length + 1) :=
    Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.list_length.comp (primrec_nodesUniv.comp Primrec.fst)))
  exact (Primrec.option_casesOn Primrec.snd hdef
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    (fun ⟨n, s⟩ => by cases s <;> rfl)

lemma cIARStep_comp {X : Type} [Primcodable X]
    {αSize : X → ℕ} {B : X → ListNBWCode} {s : X → IARCode} {a : X → ℕ}
    (hα : Primrec αSize) (hB : Primrec B) (hs : Primrec s) (ha : Primrec a) :
    Primrec (fun w => cIARStep (αSize w) (B w) (s w) (a w)) := by
  have hSome : Primrec (fun wp : X × (TreeCode × List ℕ × ℕ) =>
      cIARBuildFromRes (nodesUniv (B wp.1).1) wp.2.2.1
        (cTreeTransitionData (αSize wp.1) (B wp.1) wp.2.1 (a wp.1))) :=
    cIARBuildFromRes_comp
      (primrec_nodesUniv.comp (Primrec.fst.comp (hB.comp Primrec.fst)))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (cTreeTransitionData_comp (hα.comp Primrec.fst) (hB.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd) (ha.comp Primrec.fst))
  exact (Primrec.option_casesOn hs (Primrec.const (none : IARCode)) hSome.to₂).of_eq
    fun w => by cases s w <;> rfl

/-! #### Finite state-pool enumeration and `detListNBW` -/

def rawTreeCodes (n : ℕ) : List TreeCode :=
  ((nodesUniv n).sublists').flatMap (fun dom =>
    (dom.map (fun x => (codesSet (n + 1)).map (fun lbl => (x, lbl)))).sections)

lemma primrec_rawTreeCodes : Primrec rawTreeCodes := by
  have hinner : Primrec (fun p : ℕ × List Node =>
      p.2.map (fun x => (codesSet (p.1 + 1)).map (fun lbl => (x, lbl)))) :=
    Primrec.list_map Primrec.snd
      (Primrec.list_map
        (codesSet_primrec.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.fst)))
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂).to₂
  exact Primrec.list_flatMap (list_sublists_primrec.comp primrec_nodesUniv)
    (list_sections_primrec.comp hinner).to₂

lemma encodeHistory_mem_rawTreeCodes (n : ℕ) (H : History (Fin (n + 1))) :
    encodeHistory n H ∈ rawTreeCodes n := by
  unfold rawTreeCodes encodeHistory
  let dom := (nodesUniv n).filter (fun x =>
    @decide (x ∈ H.val.nodes) (Classical.propDecidable _))
  rw [List.mem_flatMap]
  refine ⟨dom, List.mem_sublists'.mpr List.filter_sublist, ?_⟩
  rw [List.mem_sections, List.forall₂_iff_get]
  simp only [List.length_map]
  refine ⟨rfl, fun i hi _ => ?_⟩
  simp only [List.get_eq_getElem, List.getElem_map, List.mem_map, Prod.mk.injEq]
  exact ⟨encodeSet (H.val.label dom[i]), encodeSet_mem_codesSet _, rfl, rfl⟩

def iarStatesPool (B : ListNBWCode) : List IARCode :=
  let n := B.1
  let k := (nodesUniv n).length
  let somePool := ((rawTreeCodes n).product
    ((wordsOf (List.range k) k).product (List.range (2 * k + 2)))).map Option.some
  dedupLeft (cIARInit B :: none :: somePool)

@[irreducible] def iarStates (B : ListNBWCode) : List IARCode :=
  iarStatesPool B

lemma primrec_iarStates : Primrec iarStates := by
  unfold iarStates iarStatesPool
  have hk : Primrec (fun B : ListNBWCode => (nodesUniv B.1).length) :=
    Primrec.list_length.comp (primrec_nodesUniv.comp Primrec.fst)
  have hperms : Primrec (fun B : ListNBWCode =>
      wordsOf (List.range (nodesUniv B.1).length) (nodesUniv B.1).length) :=
    wordsOf_primrec.comp (Primrec.list_range.comp hk) hk
  have hprios : Primrec (fun B : ListNBWCode => List.range (2 * (nodesUniv B.1).length + 2)) :=
    Primrec.list_range.comp
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hk) (Primrec.const 2))
  have hsome : Primrec (fun B : ListNBWCode =>
      ((rawTreeCodes B.1).product
        ((wordsOf (List.range (nodesUniv B.1).length) (nodesUniv B.1).length).product
          (List.range (2 * (nodesUniv B.1).length + 2)))).map Option.some) :=
    Primrec.list_map
      (list_product_primrec.comp (primrec_rawTreeCodes.comp Primrec.fst)
        (list_product_primrec.comp hperms hprios))
      (Primrec.option_some.comp Primrec.snd).to₂
  exact dedupLeft_primrec.comp
    (Primrec.list_cons.comp primrec_cIARInit
      (Primrec.list_cons.comp (Primrec.const (none : IARCode)) hsome))

lemma iarStates_nodup (B : ListNBWCode) : (iarStates B).Nodup := by
  unfold iarStates iarStatesPool; exact nodup_dedupLeft _

lemma iarStates_pos (B : ListNBWCode) : 0 < (iarStates B).length := by
  unfold iarStates iarStatesPool; exact dedupLeft_cons_pos _ _

lemma cIdxOf_iarStates_init (B : ListNBWCode) :
    cIdxOf (iarStates B) (cIARInit B) = 0 := by
  unfold iarStates iarStatesPool; exact cIdxOf_dedupLeft_head _ _

/-- Executable primitive-recursive compiler determinizing any `ListNBWCode` over `Fin (αSize + 1)`
into an equivalent `GenDPACode` over `Fin (αSize + 1)`. -/
def detListNBW (αSize : ℕ) (B : ListNBWCode) : GenDPACode :=
  let states := iarStates B
  let M := states.length
  let A := αSize + 1
  let trans := (List.range M).flatMap (fun sIdx =>
    (List.range A).map (fun a =>
      cIdxOf states (cIARStep αSize B (states.getD sIdx none) a)))
  let prios := (List.range M).map (fun sIdx => cIARPrio B.1 (states.getD sIdx none))
  (M - 1, trans, prios)

lemma detListNBW_comp {X : Type} [Primcodable X]
    {αSize : X → ℕ} {B : X → ListNBWCode}
    (hα : Primrec αSize) (hB : Primrec B) :
    Primrec (fun w => detListNBW (αSize w) (B w)) := by
  have hStates := primrec_iarStates.comp hB
  have hM := Primrec.list_length.comp hStates
  have hA := Primrec.succ.comp hα
  have hCell : Primrec (fun wsa : (X × ℕ) × ℕ =>
      cIdxOf (iarStates (B wsa.1.1))
        (cIARStep (αSize wsa.1.1) (B wsa.1.1)
          ((iarStates (B wsa.1.1)).getD wsa.1.2 none) wsa.2)) := by
    have hw : Primrec (fun wsa : (X × ℕ) × ℕ => wsa.1.1) := Primrec.fst.comp Primrec.fst
    have hsIdx : Primrec (fun wsa : (X × ℕ) × ℕ => wsa.1.2) := Primrec.snd.comp Primrec.fst
    have ha : Primrec (fun wsa : (X × ℕ) × ℕ => wsa.2) := Primrec.snd
    have hs := (Primrec.list_getD (none : IARCode)).comp (hStates.comp hw) hsIdx
    exact cIdxOf_primrec.comp (hStates.comp hw)
      (cIARStep_comp (hα.comp hw) (hB.comp hw) hs ha)
  have hTrans := Primrec.list_flatMap (Primrec.list_range.comp hM)
    (Primrec.list_map (Primrec.list_range.comp (hA.comp Primrec.fst)) hCell.to₂).to₂
  have hPrios := Primrec.list_map (Primrec.list_range.comp hM)
    (primrec₂_cIARPrio.comp (Primrec.fst.comp (hB.comp Primrec.fst))
      ((Primrec.list_getD (none : IARCode)).comp (hStates.comp Primrec.fst) Primrec.snd)).to₂
  exact (Primrec.nat_sub.comp hM (Primrec.const 1)).pair (hTrans.pair hPrios)

theorem primrec_detListNBW : Primrec₂ detListNBW :=
  detListNBW_comp Primrec.fst Primrec.snd

/-! #### Semantic IAR run and parity equivalence proof -/

abbrev SemPerm (k : ℕ) := {perm : List ℕ // perm.Perm (List.range k)}

abbrev SemIARState (n : ℕ) :=
  Option (History (Fin (n + 1)) × SemPerm (nodesUniv n).length × Fin (2 * (nodesUniv n).length + 2))

noncomputable def encodeIAR {n : ℕ} : SemIARState n → IARCode
  | none => none
  | some (H, perm, p) => some (encodeHistory n H, perm.val, p.val)

lemma encodeIAR_mem_iarStates (B : ListNBWCode) (S : SemIARState B.1) :
    encodeIAR S ∈ iarStates B := by
  unfold iarStates iarStatesPool
  rw [mem_dedupLeft]
  cases S with
  | none => exact List.mem_cons_of_mem _ List.mem_cons_self
  | some val =>
    rcases val with ⟨H, perm, p⟩
    apply List.mem_cons_of_mem _ (List.mem_cons_of_mem _ _)
    rw [List.mem_map]
    refine ⟨(encodeHistory B.1 H, perm.val, p.val), ?_, rfl⟩
    rw [mem_list_product_iff]
    refine ⟨encodeHistory_mem_rawTreeCodes B.1 H, ?_⟩
    rw [mem_list_product_iff]
    refine ⟨?_, List.mem_range.mpr p.isLt⟩
    rw [mem_wordsOf_iff]
    exact ⟨perm.property.length_eq.trans List.length_range,
      fun a ha => perm.property.subset ha⟩

noncomputable def semIARInit (αSize : ℕ) (B : ListNBWCode) : SemIARState B.1 :=
  let k := (nodesUniv B.1).length
  match initialHistory (toSemNBW αSize B) with
  | none => none
  | some H0 => some (H0, ⟨List.range k, List.Perm.refl _⟩, ⟨2 * k + 1, by omega⟩)

noncomputable def semIARPrio (n : ℕ) : SemIARState n → ℕ
  | none => 2 * (nodesUniv n).length + 1
  | some (_, _, p) => p.val

noncomputable def semIARStep (αSize : ℕ) (B : ListNBWCode) (S : SemIARState B.1)
    (a : Fin (αSize + 1)) : SemIARState B.1 :=
  let Bsem := toSemNBW αSize B
  let univ := nodesUniv B.1
  let k := univ.length
  match S with
  | none => none
  | some (H, perm, _) =>
    match successor Bsem H a with
    | none => none
    | some H' =>
      let isU : ℕ → Bool := fun i =>
        @decide (univ.getD i [] ∈ unstable Bsem H a) (Classical.propDecidable _)
      let isG : ℕ → Bool := fun i =>
        @decide (univ.getD i [] ∈ acceptingNodes Bsem H a) (Classical.propDecidable _)
      let uPrios := ((List.range k).filter isU).map (fun i => 2 * cIdxOf perm.val i + 1)
      let gPrios := ((List.range k).filter isG).map (fun i => 2 * cIdxOf perm.val i + 2)
      let p' := minWith (2 * k + 1) (uPrios ++ gPrios)
      have hp' : p' < 2 * k + 2 := Nat.lt_succ_of_le (minWith_le_fallback _ _)
      let perm' := perm.val.filter (fun i => !isU i) ++ perm.val.filter isU
      some (H', ⟨perm', (perm_filter_not_append_filter isU perm.val).trans perm.property⟩,
        ⟨p', hp'⟩)

noncomputable def semIARRun (αSize : ℕ) (B : ListNBWCode) (w : ℕ → Fin (αSize + 1)) :
    ℕ → SemIARState B.1
  | 0 => semIARInit αSize B
  | t + 1 => semIARStep αSize B (semIARRun αSize B w t) (w t)

lemma encodeIAR_init (αSize : ℕ) (B : ListNBWCode) :
    encodeIAR (semIARInit αSize B) = cIARInit B := by
  unfold semIARInit cIARInit
  rw [cTreeInit_eq_encode αSize B]
  cases initialHistory (toSemNBW αSize B) <;> rfl

lemma encodeIAR_prio (n : ℕ) (S : SemIARState n) :
    cIARPrio n (encodeIAR S) = semIARPrio n S := by
  cases S <;> rfl

lemma encodeIAR_step (αSize : ℕ) (B : ListNBWCode) (S : SemIARState B.1) (a : Fin (αSize + 1)) :
    cIARStep αSize B (encodeIAR S) a.val = encodeIAR (semIARStep αSize B S a) := by
  cases S with
  | none => rfl
  | some val =>
    rcases val with ⟨H, perm, p⟩
    unfold cIARStep cIARBuildFromRes semIARStep encodeIAR
    obtain ⟨hdom4, hunst, hacc, hnext⟩ := cTreeTransitionData_spec αSize B H a
    have hisU_eq : ∀ i,
        decide ((nodesUniv B.1).getD i [] ∈
          (cTreeTransitionData αSize B (encodeHistory B.1 H) a.val).2.1) =
        @decide ((nodesUniv B.1).getD i [] ∈ unstable (toSemNBW αSize B) H a)
          (Classical.propDecidable _) := by
      intro i
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq, @decide_eq_true_iff _ (Classical.propDecidable _)]
      exact hunst _
    have hisG_eq : ∀ i,
        decide ((nodesUniv B.1).getD i [] ∈
          (cTreeTransitionData αSize B (encodeHistory B.1 H) a.val).2.2.1) =
        @decide ((nodesUniv B.1).getD i [] ∈ acceptingNodes (toSemNBW αSize B) H a)
          (Classical.propDecidable _) := by
      intro i
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq, @decide_eq_true_iff _ (Classical.propDecidable _)]
      exact hacc _
    dsimp only at hnext ⊢
    by_cases hroot : ([] : Node) ∈ (cTreeTransitionData αSize B (encodeHistory B.1 H) a.val).1
    · rw [if_pos hroot] at hnext ⊢
      cases hsucc : successor (toSemNBW αSize B) H a with
      | none => rw [hsucc] at hnext; cases hnext
      | some H' =>
        rw [hsucc, Option.map_some, Option.some.injEq] at hnext
        simp only [hnext, hisU_eq, hisG_eq]
    · rw [if_neg hroot] at hnext ⊢
      cases hsucc : successor (toSemNBW αSize B) H a with
      | none => rfl
      | some H' => rw [hsucc] at hnext; cases hnext

lemma detListNBW_run_val (αSize : ℕ) (B : ListNBWCode) (w : ℕ → Fin (αSize + 1)) (t : ℕ) :
    ((toGenDPA αSize (detListNBW αSize B)).run w t).val =
      cIdxOf (iarStates B) (encodeIAR (semIARRun αSize B w t)) := by
  have hMpos : 0 < (iarStates B).length := iarStates_pos B
  have hbound : (detListNBW αSize B).1 + 1 = (iarStates B).length := by
    simp [detListNBW]; omega
  induction t with
  | zero =>
    simp only [DPA.run, toGenDPA, semIARRun, encodeIAR_init, cIdxOf_iarStates_init]
  | succ t ih =>
    change ((toGenDPA αSize (detListNBW αSize B)).step
      ((toGenDPA αSize (detListNBW αSize B)).run w t) (w t)).val = _
    change ((detListNBW αSize B).2.1.getD
      (((toGenDPA αSize (detListNBW αSize B)).run w t).val * (αSize + 1) + (w t).val) 0) %
      ((detListNBW αSize B).1 + 1) = _
    rw [ih, hbound, Nat.mul_comm _ (αSize + 1)]
    have hmem_t : encodeIAR (semIARRun αSize B w t) ∈ iarStates B :=
      encodeIAR_mem_iarStates B _
    have hs_lt : cIdxOf (iarStates B) (encodeIAR (semIARRun αSize B w t)) < (iarStates B).length :=
      cIdxOf_lt_length_of_mem hmem_t
    have hcell := flatMap_range_getD
      (fun sIdx a => cIdxOf (iarStates B) (cIARStep αSize B ((iarStates B).getD sIdx none) a))
      hs_lt (w t).isLt
    dsimp only [detListNBW]
    rw [hcell, getD_cIdxOf_of_mem none hmem_t, encodeIAR_step]
    have hmem_next : encodeIAR (semIARStep αSize B (semIARRun αSize B w t) (w t)) ∈ iarStates B :=
      encodeIAR_mem_iarStates B _
    exact Nat.mod_eq_of_lt (cIdxOf_lt_length_of_mem hmem_next)

lemma detListNBW_run_prio (αSize : ℕ) (B : ListNBWCode) (w : ℕ → Fin (αSize + 1)) (t : ℕ) :
    (toGenDPA αSize (detListNBW αSize B)).prio ((toGenDPA αSize (detListNBW αSize B)).run w t) =
      semIARPrio B.1 (semIARRun αSize B w t) := by
  change (detListNBW αSize B).2.2.getD ((toGenDPA αSize (detListNBW αSize B)).run w t).val 0 = _
  rw [detListNBW_run_val]
  have hmem : encodeIAR (semIARRun αSize B w t) ∈ iarStates B :=
    encodeIAR_mem_iarStates B _
  have hlt : cIdxOf (iarStates B) (encodeIAR (semIARRun αSize B w t)) < (iarStates B).length :=
    cIdxOf_lt_length_of_mem hmem
  dsimp only [detListNBW]
  rw [map_range_getD _ hlt, getD_cIdxOf_of_mem none hmem, encodeIAR_prio]

/-! #### Prefix stabilization and parity analysis of `semIARRun` -/

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
      dsimp only; rwa [show d + (n - d) = n by omega]
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

lemma not_parityCond_of_eventually_odd {P : ℕ → ℕ} {m : ℕ} (hodd : ¬ Even m)
    (hge : ∀ᶠ n in Filter.atTop, m ≤ P n) (hfreq : ∃ᶠ n in Filter.atTop, P n = m) :
    ¬ ParityCond P := by
  rintro ⟨p, heven, hp_freq, hp_ev⟩
  have h1 : p ≤ m := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hp_ev
    obtain ⟨n, hn, hpm⟩ := Filter.frequently_atTop.mp hfreq N
    exact hpm ▸ hN n hn
  have h2 : m ≤ p := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hge
    obtain ⟨n, hn, hpp⟩ := Filter.frequently_atTop.mp hp_freq N
    exact hpp ▸ hN n hn
  exact hodd (le_antisymm h1 h2 ▸ heven)

lemma not_even_two_mul_add_one (m : ℕ) : ¬ Even (2 * m + 1) := by
  rintro ⟨r, hr⟩; omega

lemma cIdxOf_filter_lt_of_lt {α : Type} [DecidableEq α] {l : List α} (hnodup : l.Nodup)
    (pred : α → Bool) {x y : α} (hx : x ∈ l) (hy : y ∈ l)
    (hpx : pred x = true) (hpy : pred y = true)
    (hlt : cIdxOf l x < cIdxOf l y) :
    cIdxOf (l.filter pred) x < cIdxOf (l.filter pred) y := by
  induction l with
  | nil => cases hx
  | cons a as ih =>
    obtain ⟨_, has⟩ := List.nodup_cons.mp hnodup
    by_cases hax : a = x
    · subst hax
      have hay : a ≠ y := by intro heq; subst heq; omega
      have hyas : y ∈ as := (List.mem_cons.mp hy).resolve_left hay.symm
      have hyf : y ∈ as.filter pred := List.mem_filter.mpr ⟨hyas, hpy⟩
      have _ := cIdxOf_lt_length_of_mem hyf
      simp [hpx, cIdxOf_cons, hay]
    · by_cases hay : a = y
      · subst hay; simp [cIdxOf_cons] at hlt
      · have hxas : x ∈ as := (List.mem_cons.mp hx).resolve_left (Ne.symm hax)
        have hyas : y ∈ as := (List.mem_cons.mp hy).resolve_left (Ne.symm hay)
        simp only [cIdxOf_cons, hax, hay, ↓reduceIte] at hlt
        have hlt' : cIdxOf as x < cIdxOf as y := by omega
        have hrec := ih has hxas hyas hlt'
        cases hpa : pred a
        · simpa [hpa] using hrec
        · simp [hpa, cIdxOf_cons, hax, hay, hrec]

lemma cIdxOf_append_left_of_mem {α : Type} [DecidableEq α] {l1 : List α} (l2 : List α)
    {x : α} (hx : x ∈ l1) : cIdxOf (l1 ++ l2) x = cIdxOf l1 x := by
  induction l1 with
  | nil => cases hx
  | cons a as ih =>
    simp only [List.cons_append, cIdxOf_cons]
    by_cases hax : a = x
    · simp [hax]
    · rcases List.mem_cons.mp hx with rfl | hmem
      · exact absurd rfl hax
      · simp [hax, ih hmem]

lemma cIdxOf_append_right_of_notMem {α : Type} [DecidableEq α] {l1 : List α} (l2 : List α)
    {x : α} (hx : x ∉ l1) : cIdxOf (l1 ++ l2) x = l1.length + cIdxOf l2 x := by
  induction l1 with
  | nil => simp
  | cons a as ih =>
    have hax : a ≠ x := fun heq => hx (heq ▸ List.mem_cons_self)
    have hxas : x ∉ as := fun hm => hx (List.mem_cons_of_mem _ hm)
    simp [cIdxOf_cons, hax, ih hxas, Nat.add_assoc, Nat.add_comm 1]

lemma cIdxOf_iarMove_lt_of_false_true {l : List ℕ} (isU : ℕ → Bool)
    {x y : ℕ} (hx : x ∈ l) (_hy : y ∈ l) (hux : isU x = false) (huy : isU y = true) :
    cIdxOf (l.filter (fun i => !isU i) ++ l.filter isU) x <
      cIdxOf (l.filter (fun i => !isU i) ++ l.filter isU) y := by
  have hxf : x ∈ l.filter (fun i => !isU i) := List.mem_filter.mpr ⟨hx, by simp [hux]⟩
  have hyf : y ∉ l.filter (fun i => !isU i) := by simp [huy]
  rw [cIdxOf_append_left_of_mem _ hxf, cIdxOf_append_right_of_notMem _ hyf]
  have hlt := cIdxOf_lt_length_of_mem hxf
  omega

lemma cIdxOf_iarMove_mono_of_false {l : List ℕ} (hnodup : l.Nodup) (isU : ℕ → Bool)
    {x y : ℕ} (hx : x ∈ l) (hy : y ∈ l) (hux : isU x = false)
    (hlt : cIdxOf l x < cIdxOf l y) :
    cIdxOf (l.filter (fun i => !isU i) ++ l.filter isU) x <
      cIdxOf (l.filter (fun i => !isU i) ++ l.filter isU) y := by
  cases huy : isU y
  · have hxf : x ∈ l.filter (fun i => !isU i) := List.mem_filter.mpr ⟨hx, by simp [hux]⟩
    have hyf : y ∈ l.filter (fun i => !isU i) := List.mem_filter.mpr ⟨hy, by simp [huy]⟩
    rw [cIdxOf_append_left_of_mem _ hxf, cIdxOf_append_left_of_mem _ hyf]
    exact cIdxOf_filter_lt_of_lt hnodup (fun i => !isU i) hx hy (by simp [hux]) (by simp [huy]) hlt
  · exact cIdxOf_iarMove_lt_of_false_true isU hx hy hux huy

lemma cIdxOf_eq_card_preceding {k : ℕ} {l : List ℕ} (hperm : l.Perm (List.range k))
    (x : Fin k) :
    cIdxOf l x.val = (Finset.univ.filter (fun y : Fin k => cIdxOf l y.val < cIdxOf l x.val)).card := by
  have hnodup : l.Nodup := hperm.nodup_iff.mpr List.nodup_range
  have hxm : x.val ∈ l := hperm.mem_iff.mpr (List.mem_range.mpr x.isLt)
  let r := cIdxOf l x.val
  have hrlt : r < l.length := cIdxOf_lt_length_of_mem hxm
  have heq : (Finset.univ.filter (fun y : Fin k => cIdxOf l y.val < r)) =
      (Finset.range r).attach.image (fun j =>
        ⟨l[j.val]'(lt_trans (Finset.mem_range.mp j.property) hrlt),
         List.mem_range.mp (hperm.subset (List.getElem_mem _))⟩) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_attach]
    constructor
    · intro hyr
      have hym : y.val ∈ l := hperm.mem_iff.mpr (List.mem_range.mpr y.isLt)
      refine ⟨⟨cIdxOf l y.val, Finset.mem_range.mpr hyr⟩, ?_⟩
      apply Fin.ext
      exact getElem_cIdxOf_of_mem hym
    · rintro ⟨⟨j, hj⟩, rfl⟩
      rw [cIdxOf_getElem_of_nodup hnodup j (lt_trans (Finset.mem_range.mp hj) hrlt)]
      exact Finset.mem_range.mp hj
  change r = (Finset.univ.filter (fun y : Fin k => cIdxOf l y.val < r)).card
  rw [heq, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    apply Subtype.ext
    have hv := congrArg Fin.val hab
    dsimp only at hv
    have ha := cIdxOf_getElem_of_nodup hnodup a.val (lt_trans (Finset.mem_range.mp a.property) hrlt)
    have hb := cIdxOf_getElem_of_nodup hnodup b.val (lt_trans (Finset.mem_range.mp b.property) hrlt)
    rw [hv] at ha
    exact ha.symm.trans hb

theorem detListNBW_accepts_iff (αSize : ℕ) (B : ListNBWCode) (w : ℕ → Fin (αSize + 1)) :
    (toGenDPA αSize (detListNBW αSize B)).Accepts w ↔ ListNBWAccepts αSize B w := by
  rw [← mem_semLanguage_toSemNBW]
  unfold DPA.Accepts
  have hprio_eq : (fun t => (toGenDPA αSize (detListNBW αSize B)).prio
      ((toGenDPA αSize (detListNBW αSize B)).run w t)) =
      (fun t => semIARPrio B.1 (semIARRun αSize B w t)) :=
    funext (detListNBW_run_prio αSize B w)
  rw [hprio_eq]
  let Bsem := toSemNBW αSize B
  let univ := nodesUniv B.1
  let k := univ.length
  by_cases hex_tr : ∃ ρ : ℕ → History (Fin (B.1 + 1)), IsTrace Bsem w ρ
  · obtain ⟨ρ, htr⟩ := hex_tr
    have hrun_some : ∀ t : ℕ, ∃ (perm : SemPerm k) (p : Fin (2 * k + 2)),
        semIARRun αSize B w t = some (ρ t, perm, p) := by
      intro t
      induction t with
      | zero =>
        unfold semIARRun semIARInit; rw [htr.1]
        exact ⟨⟨List.range k, List.Perm.refl _⟩, ⟨2 * k + 1, by omega⟩, rfl⟩
      | succ t ih =>
        obtain ⟨perm, p, ht⟩ := ih
        unfold semIARRun; rw [ht]; unfold semIARStep; dsimp only; rw [htr.2 t]
        exact ⟨_, _, rfl⟩
    let permAt : ℕ → SemPerm k := fun t => Classical.choose (hrun_some t)
    let prioAt : ℕ → Fin (2 * k + 2) := fun t =>
      Classical.choose (Classical.choose_spec (hrun_some t))
    have hrun_eq : ∀ t, semIARRun αSize B w t = some (ρ t, permAt t, prioAt t) :=
      fun t => Classical.choose_spec (Classical.choose_spec (hrun_some t))
    let isUAt : ℕ → ℕ → Bool := fun t i =>
      @decide (univ.getD i [] ∈ unstable Bsem (ρ t) (w t)) (Classical.propDecidable _)
    let isGAt : ℕ → ℕ → Bool := fun t i =>
      @decide (univ.getD i [] ∈ acceptingNodes Bsem (ρ t) (w t)) (Classical.propDecidable _)
    have hstep_eq : ∀ t : ℕ,
        (permAt (t + 1)).val =
          (permAt t).val.filter (fun i => !isUAt t i) ++ (permAt t).val.filter (isUAt t) ∧
        semIARPrio B.1 (semIARRun αSize B w (t + 1)) =
          minWith (2 * k + 1)
            ((((List.range k).filter (isUAt t)).map (fun i => 2 * cIdxOf (permAt t).val i + 1)) ++
             (((List.range k).filter (isGAt t)).map (fun i => 2 * cIdxOf (permAt t).val i + 2))) := by
      intro t
      have h1 := hrun_eq (t + 1)
      change semIARStep αSize B (semIARRun αSize B w t) (w t) = _ at h1
      rw [hrun_eq t] at h1
      unfold semIARStep at h1; dsimp only at h1; rw [htr.2 t] at h1
      injection h1 with hprod
      injection hprod with _ hp2
      injection hp2 with hperm_eq hprio_eq'
      refine ⟨congrArg Subtype.val hperm_eq.symm, ?_⟩
      rw [hrun_eq (t + 1), semIARPrio, ← hprio_eq']
    rw [parityCond_shift _ 1]
    let Q : ℕ → ℕ := fun t => semIARPrio B.1 (semIARRun αSize B w (1 + t))
    change ParityCond Q ↔ _
    have hQ_eq : ∀ t, Q t =
        minWith (2 * k + 1)
          ((((List.range k).filter (isUAt t)).map (fun i => 2 * cIdxOf (permAt t).val i + 1)) ++
           (((List.range k).filter (isGAt t)).map (fun i => 2 * cIdxOf (permAt t).val i + 2))) := by
      intro t
      simpa [Q, Nat.add_comm 1 t] using (hstep_eq t).2
    let Sfin : Finset (Fin k) := @Finset.filter (Fin k)
      (fun j => ∀ᶠ t in Filter.atTop, isUAt t j.val = false)
      (fun _ => Classical.propDecidable _) Finset.univ
    have hmem_Sfin : ∀ j : Fin k, j ∈ Sfin ↔ ∀ᶠ t in Filter.atTop, isUAt t j.val = false := by
      intro j; exact @Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _ |>.trans (by simp)
    have hnot_Sfin : ∀ i : Fin k, i ∉ Sfin ↔ ∃ᶠ t in Filter.atTop, isUAt t i.val = true := by
      intro i
      rw [hmem_Sfin, Filter.not_eventually]
      exact Filter.frequently_congr (Filter.Eventually.of_forall fun t => by cases isUAt t i.val <;> simp)
    have hev_Sfin : ∀ᶠ t in Filter.atTop, ∀ j ∈ Sfin, isUAt t j.val = false := by
      rw [Filter.eventually_all_finset]
      exact fun j hj => (hmem_Sfin j).mp hj
    obtain ⟨T0, hT0⟩ := Filter.eventually_atTop.mp hev_Sfin
    have hex_visit : ∀ i : Fin k, i ∉ Sfin → ∃ t ≥ T0, isUAt t i.val = true :=
      fun i hi => Filter.frequently_atTop.mp ((hnot_Sfin i).mp hi) T0
    let visitTime : Fin k → ℕ := fun i =>
      @dite _ (i ∉ Sfin) (Classical.propDecidable _)
        (fun hi => Classical.choose (hex_visit i hi) + 1) (fun _ => T0)
    let T1 : ℕ := max T0 (Finset.univ.sup visitTime)
    have hT0_le_T1 : T0 ≤ T1 := le_max_left _ _
    have hvisit_in : ∀ i : Fin k, i ∉ Sfin → ∃ t, T0 ≤ t ∧ t < T1 ∧ isUAt t i.val = true := by
      intro i hi
      have hspec := Classical.choose_spec (hex_visit i hi)
      have hvt : visitTime i ≤ T1 := le_trans (Finset.le_sup (Finset.mem_univ i)) (le_max_right _ _)
      dsimp only [visitTime] at hvt; rw [dif_pos hi] at hvt
      exact ⟨Classical.choose (hex_visit i hi), hspec.1, by omega, hspec.2⟩
    have hmem_perm : ∀ (t : ℕ) (i : Fin k), i.val ∈ (permAt t).val :=
      fun t i => (permAt t).property.mem_iff.mpr (List.mem_range.mpr i.isLt)
    have hnodup_perm : ∀ t : ℕ, (permAt t).val.Nodup :=
      fun t => (permAt t).property.nodup_iff.mpr List.nodup_range
    have hprec_persist : ∀ {j i : Fin k} {t0 : ℕ}, j ∈ Sfin → T0 ≤ t0 →
        cIdxOf (permAt t0).val j.val < cIdxOf (permAt t0).val i.val →
        ∀ d : ℕ, cIdxOf (permAt (t0 + d)).val j.val < cIdxOf (permAt (t0 + d)).val i.val := by
      intro j i t0 hj ht0 h0 d
      induction d with
      | zero => simpa using h0
      | succ d ih =>
        have hstep_perm := (hstep_eq (t0 + d)).1
        have hnext : t0 + (d + 1) = (t0 + d) + 1 := by omega
        rw [hnext, hstep_perm]
        exact cIdxOf_iarMove_mono_of_false (hnodup_perm (t0 + d)) (isUAt (t0 + d))
          (hmem_perm _ j) (hmem_perm _ i) (hT0 (t0 + d) (by omega) j hj) ih
    have hSfin_lt_Sinf : ∀ t ≥ T1, ∀ j ∈ Sfin, ∀ i : Fin k, i ∉ Sfin →
        cIdxOf (permAt t).val j.val < cIdxOf (permAt t).val i.val := by
      intro t ht j hj i hi
      obtain ⟨tv, htv0, htv1, hui⟩ := hvisit_in i hi
      have h1 : cIdxOf (permAt (tv + 1)).val j.val < cIdxOf (permAt (tv + 1)).val i.val := by
        rw [(hstep_eq tv).1]
        exact cIdxOf_iarMove_lt_of_false_true (isUAt tv)
          (hmem_perm tv j) (hmem_perm tv i) (hT0 tv htv0 j hj) hui
      simpa [show tv + 1 + (t - (tv + 1)) = t by omega] using
        hprec_persist hj (by omega) h1 (t - (tv + 1))
    have hSfin_order_const : ∀ t ≥ T1, ∀ j1 ∈ Sfin, ∀ j2 ∈ Sfin,
        (cIdxOf (permAt t).val j1.val < cIdxOf (permAt t).val j2.val ↔
         cIdxOf (permAt T1).val j1.val < cIdxOf (permAt T1).val j2.val) := by
      intro t ht j1 hj1 j2 hj2
      constructor
      · intro hlt
        rcases lt_trichotomy (cIdxOf (permAt T1).val j1.val) (cIdxOf (permAt T1).val j2.val) with
          h | heq | hgt
        · exact h
        · exfalso
          have hinj : j1.val = j2.val := by
            have e1 := getElem_cIdxOf_of_mem (hmem_perm T1 j1)
            have e2 := getElem_cIdxOf_of_mem (hmem_perm T1 j2)
            rw [← e1, ← e2]; congr 1
          rw [hinj] at hlt; exact Nat.lt_irrefl _ hlt
        · exfalso
          have hgt_t : cIdxOf (permAt t).val j2.val < cIdxOf (permAt t).val j1.val := by
            simpa [show T1 + (t - T1) = t by omega] using
              hprec_persist hj2 hT0_le_T1 hgt (t - T1)
          omega
      · intro hlt
        simpa [show T1 + (t - T1) = t by omega] using
          hprec_persist hj1 hT0_le_T1 hlt (t - T1)
    let m := Sfin.card
    have hpos_Sfin_const : ∀ t ≥ T1, ∀ j ∈ Sfin,
        cIdxOf (permAt t).val j.val = cIdxOf (permAt T1).val j.val := by
      intro t ht j hj
      rw [cIdxOf_eq_card_preceding (permAt t).property j,
          cIdxOf_eq_card_preceding (permAt T1).property j]
      congr 1; ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hy : y ∈ Sfin
      · exact hSfin_order_const t ht y hy j hj
      · constructor
        · intro hlt; exact absurd (hSfin_lt_Sinf t ht j hj y hy) (Nat.not_lt.mpr (Nat.le_of_lt hlt))
        · intro hlt; exact absurd (hSfin_lt_Sinf T1 le_rfl j hj y hy) (Nat.not_lt.mpr (Nat.le_of_lt hlt))
    have hpos_Sinf_ge : ∀ t ≥ T1, ∀ i : Fin k, i ∉ Sfin → m ≤ cIdxOf (permAt t).val i.val := by
      intro t ht i hi
      rw [cIdxOf_eq_card_preceding (permAt t).property i]
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hSfin_lt_Sinf t ht j hj i hi
    have hpos_Sfin_lt : ∀ j ∈ Sfin, cIdxOf (permAt T1).val j.val < m := by
      intro j hj
      rw [cIdxOf_eq_card_preceding (permAt T1).property j]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨j, hj, by simp⟩
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        by_contra hynot
        have := hSfin_lt_Sinf T1 le_rfl j hj y hynot
        omega
    have hGood_iff_lang :
        (∃ j ∈ Sfin, ∃ᶠ t in Filter.atTop, isGAt t j.val = true) ↔ w ∈ semLanguage Bsem := by
      constructor
      · rintro ⟨j, hjSfin, hjG⟩
        obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp ((hmem_Sfin j).mp hjSfin)
        refine lemma_9_mpr Bsem w (x := univ[j.val]) htr ⟨N0, fun t ht => ?_⟩ (fun N => ?_)
        · have hf := hN0 t ht
          have hget : univ.getD j.val [] = univ[j.val] := List.getD_eq_getElem _ _ j.isLt
          intro hmem_u
          have htrue : isUAt t j.val = true := by
            dsimp only [isUAt]; rw [hget]
            exact @decide_eq_true _ (Classical.propDecidable _) hmem_u
          rw [htrue] at hf; cases hf
        · obtain ⟨t, ht, hg⟩ := Filter.frequently_atTop.mp hjG N
          have hget : univ.getD j.val [] = univ[j.val] := List.getD_eq_getElem _ _ j.isLt
          dsimp only [isGAt] at hg; rw [hget] at hg
          exact ⟨t, ht, @of_decide_eq_true _ (Classical.propDecidable _) hg⟩
      · intro hlang
        obtain ⟨ρ', x, _, htr', ⟨N0, hstab'⟩, hacc'⟩ := lemma_9_mp Bsem w hlang
        have hρ_eq : ∀ t, ρ' t = ρ t := by
          intro t
          induction t with
          | zero => exact Option.some.inj (htr'.1.symm.trans htr.1)
          | succ t ih =>
            have hs1 := htr'.2 t; rw [ih, htr.2 t] at hs1; exact Option.some.inj hs1.symm
        obtain ⟨t_wit, _, hx_acc⟩ := hacc' 0
        have hx_mem : x ∈ (ρ t_wit).val.nodes := by
          rw [← hρ_eq t_wit]; exact (Finset.mem_filter.mp hx_acc).1
        have hx_univ : x ∈ univ := mem_nodesUniv_of_history (ρ t_wit) hx_mem
        let j : Fin k := ⟨cIdxOf univ x, cIdxOf_lt_length_of_mem hx_univ⟩
        have hj_get : univ.getD j.val [] = x := getD_cIdxOf_of_mem [] hx_univ
        refine ⟨j, ?_, ?_⟩
        · rw [hmem_Sfin, Filter.eventually_atTop]
          refine ⟨N0, fun t ht => ?_⟩
          dsimp only [isUAt]; rw [hj_get, ← hρ_eq t]
          exact Bool.eq_false_iff.mpr fun htr_u =>
            hstab' t ht (@of_decide_eq_true _ (Classical.propDecidable _) htr_u)
        · rw [Filter.frequently_atTop]
          intro N
          obtain ⟨t, ht, hxt⟩ := hacc' N
          refine ⟨t, ht, ?_⟩
          dsimp only [isGAt]; rw [hj_get, ← hρ_eq t]
          exact @decide_eq_true _ (Classical.propDecidable _) hxt
    rw [← hGood_iff_lang]
    by_cases hex_good : ∃ j ∈ Sfin, ∃ᶠ t in Filter.atTop, isGAt t j.val = true
    · simp only [hex_good, iff_true]
      let GoodSet : Finset (Fin k) := @Finset.filter (Fin k)
        (fun j => ∃ᶠ t in Filter.atTop, isGAt t j.val = true)
        (fun _ => Classical.propDecidable _) Sfin
      have hmem_Good : ∀ j : Fin k, j ∈ GoodSet ↔
          j ∈ Sfin ∧ ∃ᶠ t in Filter.atTop, isGAt t j.val = true :=
        fun j => @Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _
      obtain ⟨j0, hj0S, hj0G⟩ := hex_good
      have hGood_ne : GoodSet.Nonempty := ⟨j0, (hmem_Good j0).mpr ⟨hj0S, hj0G⟩⟩
      let rStar : ℕ := (GoodSet.image (fun j => cIdxOf (permAt T1).val j.val)).min'
        (hGood_ne.image _)
      obtain ⟨jStar, hjStarGood, hrStar_eq⟩ := Finset.mem_image.mp
        (Finset.min'_mem (GoodSet.image (fun j => cIdxOf (permAt T1).val j.val)) (hGood_ne.image _))
      obtain ⟨hjStarSfin, hjStarFreq⟩ := (hmem_Good jStar).mp hjStarGood
      have hrStar_eq' : cIdxOf (permAt T1).val jStar.val = rStar := hrStar_eq
      have hrStar_lt_m : rStar < m := by
        rw [← hrStar_eq']; exact hpos_Sfin_lt jStar hjStarSfin
      have hm_le_k : m ≤ k := by simpa [m, k] using Finset.card_le_univ Sfin
      let FrontBad := Sfin.filter (fun j => cIdxOf (permAt T1).val j.val < rStar)
      have hev_noG : ∀ᶠ t in Filter.atTop, ∀ j ∈ FrontBad, isGAt t j.val = false := by
        rw [Filter.eventually_all_finset]
        intro j hj
        obtain ⟨hjS, hjlt⟩ := Finset.mem_filter.mp hj
        have hjnotGood : j ∉ GoodSet := by
          intro hg
          have hle := Finset.min'_le (GoodSet.image (fun z => cIdxOf (permAt T1).val z.val))
            _ (Finset.mem_image_of_mem _ hg)
          change rStar ≤ cIdxOf (permAt T1).val j.val at hle; omega
        have hnotfreq : ¬ ∃ᶠ t in Filter.atTop, isGAt t j.val = true :=
          fun hf => hjnotGood ((hmem_Good j).mpr ⟨hjS, hf⟩)
        rw [Filter.not_frequently] at hnotfreq
        exact hnotfreq.mono fun t ht => Bool.eq_false_iff.mpr ht
      obtain ⟨T2_raw, hT2_raw⟩ := Filter.eventually_atTop.mp hev_noG
      let T2 := max T1 T2_raw
      have hQ_ge : ∀ t ≥ T2, 2 * rStar + 2 ≤ Q t := by
        intro t ht
        have ht1 : T1 ≤ t := le_trans (le_max_left _ _) ht
        have ht0 : T0 ≤ t := le_trans hT0_le_T1 ht1
        have ht2 : T2_raw ≤ t := le_trans (le_max_right _ _) ht
        rw [hQ_eq t, le_minWith_iff]
        refine ⟨by omega, ?_⟩
        intro r hr
        rcases List.mem_append.mp hr with hru | hrg
        · obtain ⟨i, hi_flt, rfl⟩ := List.mem_map.mp hru
          obtain ⟨hi_rng, hi_u⟩ := List.mem_filter.mp hi_flt
          let iFin : Fin k := ⟨i, List.mem_range.mp hi_rng⟩
          have hinot : iFin ∉ Sfin := fun his => by rw [hT0 t ht0 iFin his] at hi_u; cases hi_u
          have hge := hpos_Sinf_ge t ht1 iFin hinot
          change m ≤ cIdxOf (permAt t).val i at hge; omega
        · obtain ⟨i, hi_flt, rfl⟩ := List.mem_map.mp hrg
          obtain ⟨hi_rng, hi_g⟩ := List.mem_filter.mp hi_flt
          let iFin : Fin k := ⟨i, List.mem_range.mp hi_rng⟩
          by_cases his : iFin ∈ Sfin
          · have hpos_eq : cIdxOf (permAt t).val i = cIdxOf (permAt T1).val iFin.val :=
              hpos_Sfin_const t ht1 iFin his
            rw [hpos_eq]
            by_contra hlt_r
            have hfb : iFin ∈ FrontBad := Finset.mem_filter.mpr ⟨his, by omega⟩
            have hfalse := hT2_raw t ht2 iFin hfb
            change isGAt t i = false at hfalse; rw [hfalse] at hi_g; cases hi_g
          · have hge := hpos_Sinf_ge t ht1 iFin his
            change m ≤ cIdxOf (permAt t).val i at hge; omega
      refine ⟨2 * rStar + 2, ⟨rStar + 1, by ring⟩, ?_, Filter.eventually_atTop.mpr ⟨T2, hQ_ge⟩⟩
      rw [Filter.frequently_atTop]
      intro N
      obtain ⟨t, ht, hg⟩ := Filter.frequently_atTop.mp hjStarFreq (max N T2)
      have htN : N ≤ t := le_trans (le_max_left _ _) ht
      have ht2 : T2 ≤ t := le_trans (le_max_right _ _) ht
      have ht1 : T1 ≤ t := le_trans (le_max_left _ _) ht2
      refine ⟨t, htN, le_antisymm ?_ (hQ_ge t ht2)⟩
      change Q t ≤ 2 * rStar + 2
      rw [hQ_eq t]
      apply minWith_le_of_mem
      apply List.mem_append_right
      rw [List.mem_map]
      refine ⟨jStar.val, List.mem_filter.mpr ⟨List.mem_range.mpr jStar.isLt, hg⟩, ?_⟩
      rw [hpos_Sfin_const t ht1 jStar hjStarSfin, hrStar_eq']
    · simp only [hex_good, iff_false]
      have hev_all_noG : ∀ᶠ t in Filter.atTop, ∀ j ∈ Sfin, isGAt t j.val = false := by
        rw [Filter.eventually_all_finset]
        intro j hj
        have hnotf : ¬ ∃ᶠ t in Filter.atTop, isGAt t j.val = true := fun hf => hex_good ⟨j, hj, hf⟩
        rw [Filter.not_frequently] at hnotf
        exact hnotf.mono fun t ht => Bool.eq_false_iff.mpr ht
      obtain ⟨T2_raw, hT2_raw⟩ := Filter.eventually_atTop.mp hev_all_noG
      let T2 := max T1 T2_raw
      have hm_le_k : m ≤ k := by simpa [m, k] using Finset.card_le_univ Sfin
      rcases Nat.eq_or_lt_of_le hm_le_k with hmk | hm_lt_k
      · have hall_Sfin : ∀ i : Fin k, i ∈ Sfin := by
          have heq_univ : Sfin = Finset.univ :=
            Finset.eq_univ_of_card Sfin (by simpa [m, k] using hmk)
          intro i; rw [heq_univ]; exact Finset.mem_univ i
        have hQ_const : ∀ t ≥ T2, Q t = 2 * k + 1 := by
          intro t ht
          have ht0 : T0 ≤ t := le_trans hT0_le_T1 (le_trans (le_max_left _ _) ht)
          have ht2 : T2_raw ≤ t := le_trans (le_max_right _ _) ht
          rw [hQ_eq t]
          have hu_nil : (List.range k).filter (isUAt t) = [] := by
            rw [List.filter_eq_nil_iff]; intro i hi
            let iFin : Fin k := ⟨i, List.mem_range.mp hi⟩
            rw [hT0 t ht0 iFin (hall_Sfin iFin)]; simp
          have hg_nil : (List.range k).filter (isGAt t) = [] := by
            rw [List.filter_eq_nil_iff]; intro i hi
            let iFin : Fin k := ⟨i, List.mem_range.mp hi⟩
            rw [hT2_raw t ht2 iFin (hall_Sfin iFin)]; simp
          simp [hu_nil, hg_nil, minWith]
        apply not_parityCond_of_eventually_odd (m := 2 * k + 1) (not_even_two_mul_add_one k)
        · exact Filter.eventually_atTop.mpr ⟨T2, fun t ht => by rw [hQ_const t ht]⟩
        · rw [Filter.frequently_atTop]
          exact fun N => ⟨max N T2, le_max_left _ _, hQ_const _ (le_max_right _ _)⟩
      · have hQ_ge_odd : ∀ t ≥ T2, 2 * m + 1 ≤ Q t := by
          intro t ht
          have ht1 : T1 ≤ t := le_trans (le_max_left _ _) ht
          have ht0 : T0 ≤ t := le_trans hT0_le_T1 ht1
          have ht2 : T2_raw ≤ t := le_trans (le_max_right _ _) ht
          rw [hQ_eq t, le_minWith_iff]
          refine ⟨by omega, ?_⟩
          intro r hr
          rcases List.mem_append.mp hr with hru | hrg
          · obtain ⟨i, hi_flt, rfl⟩ := List.mem_map.mp hru
            obtain ⟨hi_rng, hi_u⟩ := List.mem_filter.mp hi_flt
            let iFin : Fin k := ⟨i, List.mem_range.mp hi_rng⟩
            have hinot : iFin ∉ Sfin := fun his => by rw [hT0 t ht0 iFin his] at hi_u; cases hi_u
            have hge := hpos_Sinf_ge t ht1 iFin hinot
            change m ≤ cIdxOf (permAt t).val i at hge; omega
          · obtain ⟨i, hi_flt, rfl⟩ := List.mem_map.mp hrg
            obtain ⟨hi_rng, hi_g⟩ := List.mem_filter.mp hi_flt
            let iFin : Fin k := ⟨i, List.mem_range.mp hi_rng⟩
            have hinot : iFin ∉ Sfin := fun his => by rw [hT2_raw t ht2 iFin his] at hi_g; cases hi_g
            have hge := hpos_Sinf_ge t ht1 iFin hinot
            change m ≤ cIdxOf (permAt t).val i at hge; omega
        apply not_parityCond_of_eventually_odd (m := 2 * m + 1) (not_even_two_mul_add_one m)
          (Filter.eventually_atTop.mpr ⟨T2, hQ_ge_odd⟩)
        rw [Filter.frequently_atTop]
        intro N
        let t0 := max N T2
        have ht0_T2 : T2 ≤ t0 := le_max_right _ _
        have ht0_T1 : T1 ≤ t0 := le_trans (le_max_left _ _) ht0_T2
        have hlen_t0 : (permAt t0).val.length = k :=
          (permAt t0).property.length_eq.trans List.length_range
        have hm_lt_len : m < (permAt t0).val.length := by rw [hlen_t0]; exact hm_lt_k
        let i0Val : ℕ := (permAt t0).val[m]
        let i0 : Fin k :=
          ⟨i0Val, List.mem_range.mp ((permAt t0).property.subset (List.getElem_mem hm_lt_len))⟩
        have hi0_pos0 : cIdxOf (permAt t0).val i0.val = m :=
          cIdxOf_getElem_of_nodup (hnodup_perm t0) m hm_lt_len
        have hi0_notSfin : i0 ∉ Sfin := by
          intro his
          have hc := hpos_Sfin_const t0 ht0_T1 i0 his
          have hlt := hpos_Sfin_lt i0 his
          omega
        have hex_d : ∃ d : ℕ, isUAt (t0 + d) i0.val = true := by
          obtain ⟨t, ht, hu⟩ := Filter.frequently_atTop.mp ((hnot_Sfin i0).mp hi0_notSfin) t0
          exact ⟨t - t0, by simpa [show t0 + (t - t0) = t by omega] using hu⟩
        let d0 := Nat.find hex_d
        have hd0_true : isUAt (t0 + d0) i0.val = true := Nat.find_spec hex_d
        have hd0_min : ∀ d < d0, isUAt (t0 + d) i0.val = false :=
          fun d hd => Bool.eq_false_iff.mpr (Nat.find_min hex_d hd)
        have hstay_m : ∀ d ≤ d0, cIdxOf (permAt (t0 + d)).val i0.val = m := by
          intro d
          induction d with
          | zero => intro _; simpa using hi0_pos0
          | succ d ih =>
            intro hdle
            have hd_pos : cIdxOf (permAt (t0 + d)).val i0.val = m := ih (by omega)
            have his_false : isUAt (t0 + d) i0.val = false := hd0_min d (by omega)
            have hnext_eq : t0 + (d + 1) = (t0 + d) + 1 := by omega
            rw [hnext_eq]
            have hge_m : m ≤ cIdxOf (permAt ((t0 + d) + 1)).val i0.val :=
              hpos_Sinf_ge ((t0 + d) + 1) (by omega) i0 hi0_notSfin
            apply le_antisymm _ hge_m
            rw [cIdxOf_eq_card_preceding (permAt ((t0 + d) + 1)).property i0,
                ← hd_pos,
                cIdxOf_eq_card_preceding (permAt (t0 + d)).property i0]
            apply Finset.card_le_card
            intro y hy
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
            by_contra hnot_lt
            have hy_ne : y ≠ i0 := fun heq => by subst heq; exact Nat.lt_irrefl _ hy
            have hgt : cIdxOf (permAt (t0 + d)).val i0.val < cIdxOf (permAt (t0 + d)).val y.val := by
              rcases lt_trichotomy (cIdxOf (permAt (t0 + d)).val y.val)
                (cIdxOf (permAt (t0 + d)).val i0.val) with h1 | h2 | h3
              · exact absurd h1 hnot_lt
              · exfalso
                have e1 := getElem_cIdxOf_of_mem (hmem_perm (t0 + d) y)
                have e2 := getElem_cIdxOf_of_mem (hmem_perm (t0 + d) i0)
                apply hy_ne; apply Fin.ext; rw [← e1, ← e2]; congr 1
              · exact h3
            have hmono := cIdxOf_iarMove_mono_of_false (hnodup_perm (t0 + d)) (isUAt (t0 + d))
              (hmem_perm _ i0) (hmem_perm _ y) his_false hgt
            rw [← (hstep_eq (t0 + d)).1] at hmono
            omega
        have hpos_d0 : cIdxOf (permAt (t0 + d0)).val i0.val = m := hstay_m d0 le_rfl
        refine ⟨t0 + d0, by have := le_max_left N T2; omega, ?_⟩
        apply le_antisymm _ (hQ_ge_odd (t0 + d0) (by omega))
        change Q (t0 + d0) ≤ 2 * m + 1
        rw [hQ_eq (t0 + d0)]
        apply minWith_le_of_mem
        apply List.mem_append_left
        rw [List.mem_map]
        refine ⟨i0.val, List.mem_filter.mpr ⟨List.mem_range.mpr i0.isLt, hd0_true⟩, ?_⟩
        rw [hpos_d0]
  · have hnot_lang : w ∉ semLanguage Bsem := by
      intro hlang
      obtain ⟨ρ, _, _, htr, _, _⟩ := lemma_9_mp Bsem w hlang
      exact hex_tr ⟨ρ, htr⟩
    rw [iff_false_right hnot_lang]
    have hev_none : ∃ T : ℕ, semIARRun αSize B w T = none := by
      by_contra hall_some
      have hex_H : ∀ t : ℕ, ∃ (H : History (Fin (B.1 + 1))) (perm : SemPerm k) (p : Fin (2 * k + 2)),
          semIARRun αSize B w t = some (H, perm, p) := by
        intro t
        cases hr : semIARRun αSize B w t with
        | none => exact absurd ⟨t, hr⟩ hall_some
        | some val => rcases val with ⟨H, perm, p⟩; exact ⟨H, perm, p, rfl⟩
      let ρ : ℕ → History (Fin (B.1 + 1)) := fun t => Classical.choose (hex_H t)
      apply hex_tr
      refine ⟨ρ, ?_, ?_⟩
      · obtain ⟨perm0, p0, h0⟩ := Classical.choose_spec (hex_H 0)
        change semIARInit αSize B = some (ρ 0, perm0, p0) at h0
        unfold semIARInit at h0
        dsimp only at h0
        change initialHistory (toSemNBW αSize B) = some (ρ 0)
        cases hinit : initialHistory (toSemNBW αSize B) with
        | none => rw [hinit] at h0; cases h0
        | some H0 =>
          rw [hinit] at h0
          injection h0 with hprod
          exact congrArg Option.some (congrArg Prod.fst hprod)
      · intro t
        obtain ⟨permt, pt, ht⟩ := Classical.choose_spec (hex_H t)
        obtain ⟨permt1, pt1, ht1⟩ := Classical.choose_spec (hex_H (t + 1))
        change semIARStep αSize B (semIARRun αSize B w t) (w t) = some (ρ (t + 1), permt1, pt1) at ht1
        rw [ht] at ht1; unfold semIARStep at ht1; dsimp only at ht1
        change successor (toSemNBW αSize B) (ρ t) (w t) = some (ρ (t + 1))
        cases hsucc : successor (toSemNBW αSize B) (ρ t) (w t) with
        | none => rw [hsucc] at ht1; cases ht1
        | some H' =>
          rw [hsucc] at ht1
          injection ht1 with hprod
          exact congrArg Option.some (congrArg Prod.fst hprod)
    obtain ⟨T, hT⟩ := hev_none
    have hall_none : ∀ d : ℕ, semIARRun αSize B w (T + d) = none := by
      intro d
      induction d with
      | zero => simpa using hT
      | succ d ih =>
        have h1 : T + (d + 1) = (T + d) + 1 := by omega
        rw [h1, semIARRun, ih]; rfl
    have hprio_odd : ∀ t ≥ T, semIARPrio B.1 (semIARRun αSize B w t) = 2 * k + 1 := by
      intro t ht
      have hnone : semIARRun αSize B w t = none := by
        simpa [show T + (t - T) = t by omega] using hall_none (t - T)
      rw [hnone]; rfl
    apply not_parityCond_of_eventually_odd (m := 2 * k + 1) (not_even_two_mul_add_one k)
    · exact Filter.eventually_atTop.mpr ⟨T, fun t ht => by rw [hprio_odd t ht]⟩
    · rw [Filter.frequently_atTop]
      exact fun N => ⟨max N T, le_max_left _ _, hprio_odd _ (le_max_right _ _)⟩

end ExecutableHistory

/-! ### Section 3: Bitmask `NBWCode := ℕ × ℕ × List ℕ × ℕ` Interface and `detNBW` -/

/-- Bitmask description of a nondeterministic Büchi automaton over `Fin (αSize + 1)`:
`(maxState, initMask, transMasks, accMask)` describes the NBW with state space `Fin (b.1 + 1)`,
initial states `{q | Nat.testBit b.2.1 q.val = true}`, transitions
`q' ∈ delta q a ↔ Nat.testBit (b.2.2.1.getD (q.val * (αSize + 1) + a.val) 0) q'.val = true`,
and accepting states `{q | Nat.testBit b.2.2.2 q.val = true}`. -/
abbrev NBWCode : Type := ℕ × ℕ × List ℕ × ℕ

/-- Acceptance of an infinite word `w : ℕ → Fin (αSize + 1)` by a bitmask `NBWCode` `b`. -/
def NBWAccepts (αSize : ℕ) (b : NBWCode) (w : ℕ → Fin (αSize + 1)) : Prop :=
  ∃ ρ : ℕ → Fin (b.1 + 1),
    Nat.testBit b.2.1 (ρ 0).val = true ∧
    (∀ n, Nat.testBit (b.2.2.1.getD ((ρ n).val * (αSize + 1) + (w n).val) 0)
      (ρ (n + 1)).val = true) ∧
    ∃ᶠ n in Filter.atTop, Nat.testBit b.2.2.2 (ρ n).val = true

lemma NBWAccepts_iff_exists_state (αSize : ℕ) (b : NBWCode) (w : ℕ → Fin (αSize + 1)) :
    NBWAccepts αSize b w ↔
      ∃ ρ : ℕ → Fin (b.1 + 1),
        Nat.testBit b.2.1 (ρ 0).val = true ∧
        (∀ n, Nat.testBit (b.2.2.1.getD ((ρ n).val * (αSize + 1) + (w n).val) 0)
          (ρ (n + 1)).val = true) ∧
        ∃ q : Fin (b.1 + 1), Nat.testBit b.2.2.2 q.val = true ∧ ∃ᶠ n in Filter.atTop, ρ n = q := by
  constructor
  · rintro ⟨ρ, h0, hstep, hfreq⟩
    obtain ⟨q, hq, hqfreq⟩ :=
      exists_inf_state_of_frequently (fun q : Fin (b.1 + 1) => Nat.testBit b.2.2.2 q.val = true)
        ρ hfreq
    exact ⟨ρ, h0, hstep, q, hq, hqfreq⟩
  · rintro ⟨ρ, h0, hstep, q, hq, hfreq⟩
    exact ⟨ρ, h0, hstep, hfreq.mono fun n hn => hn ▸ hq⟩

def cDivPow2 (mask q : ℕ) : ℕ :=
  (List.range q).foldl (fun acc _ => acc / 2) mask

def cTestBit (mask q : ℕ) : Bool :=
  decide (cDivPow2 mask q % 2 = 1)

lemma primrec₂_cDivPow2 : Primrec₂ cDivPow2 :=
  Primrec.list_foldl (Primrec.list_range.comp Primrec.snd) Primrec.fst
    (Primrec.nat_div.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 2)).to₂

lemma primrec₂_cTestBit : Primrec₂ cTestBit :=
  (Primrec.eq.comp (Primrec.nat_mod.comp primrec₂_cDivPow2 (Primrec.const 2))
    (Primrec.const 1)).decide

lemma cDivPow2_eq (mask q : ℕ) : cDivPow2 mask q = mask / 2 ^ q := by
  induction q with
  | zero => simp [cDivPow2]
  | succ q ih =>
    simp only [cDivPow2, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change cDivPow2 mask q / 2 = mask / 2 ^ (q + 1)
    rw [ih, Nat.div_div_eq_div_mul, Nat.pow_succ]

lemma cTestBit_eq_testBit (mask q : ℕ) : cTestBit mask q = Nat.testBit mask q := by
  unfold cTestBit
  rw [cDivPow2_eq, Nat.testBit_eq_decide_div_mod_eq]

def maskToList (S mask : ℕ) : List ℕ :=
  (List.range S).filter (fun q => cTestBit mask q)

lemma primrec₂_maskToList : Primrec₂ maskToList := by
  have hp : PrimrecPred (fun p : (ℕ × ℕ) × ℕ => cTestBit p.1.2 p.2 = true) :=
    Primrec.eq.comp (primrec₂_cTestBit.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
      (Primrec.const true)
  exact (filter_primrec (Primrec.list_range.comp Primrec.fst) hp).of_eq fun ⟨S, mask⟩ => by
    simp [maskToList]

lemma mem_maskToList_iff {S : ℕ} (mask : ℕ) (q : Fin S) :
    q.val ∈ maskToList S mask ↔ Nat.testBit mask q.val = true := by
  simp [maskToList, q.isLt, cTestBit_eq_testBit]

def nbwToListNBW (αSize : ℕ) (b : NBWCode) : ListNBWCode :=
  let S := b.1 + 1
  let A := αSize + 1
  let init := maskToList S b.2.1
  let acc := maskToList S b.2.2.2
  let trans := (List.range S).flatMap (fun q =>
    (List.range A).map (fun a =>
      maskToList S (b.2.2.1.getD (q * A + a) 0)))
  (b.1, init, trans, acc)

lemma primrec₂_nbwToListNBW : Primrec₂ nbwToListNBW := by
  have hA : Primrec (fun p : ℕ × NBWCode => p.1 + 1) := Primrec.succ.comp Primrec.fst
  have hb : Primrec (fun p : ℕ × NBWCode => p.2) := Primrec.snd
  have hS : Primrec (fun p : ℕ × NBWCode => p.2.1 + 1) := Primrec.succ.comp (Primrec.fst.comp hb)
  have hInit : Primrec (fun p : ℕ × NBWCode => maskToList (p.2.1 + 1) p.2.2.1) :=
    primrec₂_maskToList.comp hS (Primrec.fst.comp (Primrec.snd.comp hb))
  have hAcc : Primrec (fun p : ℕ × NBWCode => maskToList (p.2.1 + 1) p.2.2.2.2) :=
    primrec₂_maskToList.comp hS (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hb)))
  have hCell : Primrec (fun x : ((ℕ × NBWCode) × ℕ) × ℕ =>
      let p := x.1.1
      let q := x.1.2
      let a := x.2
      maskToList (p.2.1 + 1) (p.2.2.2.1.getD (q * (p.1 + 1) + a) 0)) := by
    have hp : Primrec (fun x : ((ℕ × NBWCode) × ℕ) × ℕ => x.1.1) :=
      Primrec.fst.comp Primrec.fst
    have hq : Primrec (fun x : ((ℕ × NBWCode) × ℕ) × ℕ => x.1.2) :=
      Primrec.snd.comp Primrec.fst
    have ha : Primrec (fun x : ((ℕ × NBWCode) × ℕ) × ℕ => x.2) := Primrec.snd
    have hIdx := Primrec.nat_add.comp (Primrec.nat_mul.comp hq (hA.comp hp)) ha
    have hMask := (Primrec.list_getD 0).comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (hb.comp hp)))) hIdx
    exact primrec₂_maskToList.comp (hS.comp hp) hMask
  have hTrans : Primrec (fun p : ℕ × NBWCode =>
      (List.range (p.2.1 + 1)).flatMap (fun q =>
        (List.range (p.1 + 1)).map (fun a =>
          maskToList (p.2.1 + 1) (p.2.2.2.1.getD (q * (p.1 + 1) + a) 0)))) :=
    Primrec.list_flatMap (Primrec.list_range.comp hS)
      (Primrec.list_map (Primrec.list_range.comp (hA.comp Primrec.fst)) hCell.to₂).to₂
  exact (Primrec.fst.comp hb).pair (hInit.pair (hTrans.pair hAcc))

lemma ListNBWAccepts_nbwToListNBW (αSize : ℕ) (b : NBWCode) (w : ℕ → Fin (αSize + 1)) :
    ListNBWAccepts αSize (nbwToListNBW αSize b) w ↔ NBWAccepts αSize b w := by
  rw [ListNBWAccepts_iff_frequently]
  unfold NBWAccepts nbwToListNBW
  dsimp only
  refine exists_congr fun ρ => ?_
  rw [mem_maskToList_iff b.2.1 (ρ 0)]
  refine and_congr_right fun _ => and_congr ?_ ?_
  · refine forall_congr' fun n => ?_
    rw [flatMap_range_getD_list _ (ρ n).isLt (w n).isLt,
      mem_maskToList_iff _ (ρ (n + 1))]
  · exact Filter.frequently_congr (Filter.Eventually.of_forall fun n =>
      mem_maskToList_iff b.2.2.2 (ρ n))

/-- Executable primitive-recursive compiler determinizing any bitmask `NBWCode` over
`Fin (αSize + 1)` into an equivalent `GenDPACode` over `Fin (αSize + 1)`. -/
def detNBW (αSize : ℕ) (b : NBWCode) : GenDPACode :=
  detListNBW αSize (nbwToListNBW αSize b)

theorem primrec_detNBW : Primrec₂ detNBW :=
  primrec_detListNBW.comp Primrec.fst primrec₂_nbwToListNBW

theorem detNBW_accepts_iff (αSize : ℕ) (b : NBWCode) (w : ℕ → Fin (αSize + 1)) :
    (toGenDPA αSize (detNBW αSize b)).Accepts w ↔ NBWAccepts αSize b w :=
  (detListNBW_accepts_iff αSize (nbwToListNBW αSize b) w).trans
    (ListNBWAccepts_nbwToListNBW αSize b w)

end DistLTLSynth.Char.Thm34NBWAux

open DistLTLSynth.Char DistLTLSynth.Char.Thm34NBWAux in
theorem solution :
    (∃ detNBW : ℕ → DistLTLSynth.Char.NBWCode → DistLTLSynth.Char.GenDPACode, Primrec₂ detNBW ∧
      ∀ (αSize : ℕ) (b : DistLTLSynth.Char.NBWCode) (w : ℕ → Fin (αSize + 1)),
        (DistLTLSynth.Char.toGenDPA αSize (detNBW αSize b)).Accepts w ↔
          DistLTLSynth.Char.NBWAccepts αSize b w) ∧
    (∃ detListNBW : ℕ → DistLTLSynth.Char.ListNBWCode → DistLTLSynth.Char.GenDPACode, Primrec₂ detListNBW ∧
      ∀ (αSize : ℕ) (B : DistLTLSynth.Char.ListNBWCode) (w : ℕ → Fin (αSize + 1)),
        (DistLTLSynth.Char.toGenDPA αSize (detListNBW αSize B)).Accepts w ↔
          DistLTLSynth.Char.ListNBWAccepts αSize B w) :=
  ⟨⟨Thm34NBWAux.detNBW, Thm34NBWAux.primrec_detNBW, Thm34NBWAux.detNBW_accepts_iff⟩,
   ⟨Thm34NBWAux.detListNBW, Thm34NBWAux.primrec_detListNBW, Thm34NBWAux.detListNBW_accepts_iff⟩⟩
