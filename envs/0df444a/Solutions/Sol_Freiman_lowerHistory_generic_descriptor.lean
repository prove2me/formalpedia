-- Prove2me | solution 1 for Freiman.lowerHistory_generic_descriptor
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T16:22:38.850367+00:00
-- url     : https://prove2.me/submissions/b6fd168a-0072-4901-ae67-d58257119507

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.LinearCombination

set_option Elab.async false
set_option linter.all false

-- Source: agents.genericdesc16.Replay
open Freiman
namespace GenericDesc16
attribute [local instance] Classical.propDecidable

private noncomputable def wideAt (h : ℕ → LowerPair) (j : ℕ) (flip : Bool) : Bool :=
  ((lowerOrientation h j).xor (lowerReflects (h j))).xor flip

private noncomputable def trace (h : ℕ → LowerPair) (labels : ℕ → LowerLabel) (start : ℕ) :
    ℕ → List (LowerLabel × Bool)
  | 0 => []
  | n+1 => trace h labels start n ++ [(labels (start+n), lowerReflects (h (start+n+1)))]

@[simp] theorem trace_length (h : ℕ → LowerPair) (labels : ℕ → LowerLabel) (start n : ℕ) :
    (trace h labels start n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [trace, ih]

private theorem normalize_reflect (p : LowerPair) :
    lowerNormalize p = if lowerReflects p then p.swap else p := by
  rcases p with ⟨p,q⟩
  unfold lowerNormalize lowerReflects
  by_cases h : lowerWidth q ≤ lowerWidth p
  · have hn : ¬ lowerWidth p < lowerWidth q := not_lt.mpr h
    simp [h, hn]
  · have hl : lowerWidth p < lowerWidth q := lt_of_not_ge h
    simp [h, hl, Prod.swap]

private theorem normalize_physical (h : ℕ → LowerPair) (j : ℕ) (flip : Bool) :
    lowerNormalize (h j) = lowerHistoryOrient
      (lowerHistoryOrient (lowerPhysicalPath h j) flip) (wideAt h j flip) := by
  cases ho : lowerOrientation h j <;> cases hr : lowerReflects (h j) <;> cases flip <;>
    simp [lowerHistoryOrient, lowerPhysicalPath, wideAt, normalize_reflect, ho, hr, Prod.swap]

private theorem compatible_physical (h : ℕ → LowerPair) (j : ℕ) (flip : Bool) :
    lowerHistoryWiderCompatible (lowerHistoryOrient (lowerPhysicalPath h j) flip)
      (wideAt h j flip) := by
  have hn : lowerWidth (lowerNormalize (h j)).2 ≤ lowerWidth (lowerNormalize (h j)).1 := by
    unfold lowerNormalize
    split_ifs with h <;> simp_all [le_of_not_ge]
  rw [normalize_physical h j flip] at hn
  cases hw : wideAt h j flip <;> simpa [lowerHistoryWiderCompatible, lowerHistoryOrient, hw] using hn

private theorem physical_step (h : ℕ → LowerPair) (j : ℕ) (l : LowerLabel) (flip : Bool)
    (hc : h (j+1) = lowerChild (h j) l) :
    lowerHistoryOrient (lowerPhysicalPath h (j+1)) flip =
      lowerHistoryRawStep (lowerHistoryOrient (lowerPhysicalPath h j) flip)
        (wideAt h j flip) l := by
  cases ho : lowerOrientation h j <;> cases hr : lowerReflects (h j) <;> cases flip <;>
    simp [lowerPhysicalPath, lowerOrientation, hc, lowerChild, normalize_reflect,
      lowerHistoryOrient, lowerHistoryRawStep, wideAt, ho, hr, Prod.swap]

private theorem wide_next (h : ℕ → LowerPair) (j : ℕ) (flip : Bool) :
    wideAt h (j+1) flip =
      if lowerReflects (h (j+1)) then !(wideAt h j flip) else wideAt h j flip := by
  cases ho : lowerOrientation h j <;> cases hr : lowerReflects (h j) <;>
    cases hrn : lowerReflects (h (j+1)) <;> cases flip <;>
    simp [wideAt, lowerOrientation, ho, hr, hrn]

private theorem trace_take (h : ℕ → LowerPair) (labels : ℕ → LowerLabel) (start n j : ℕ)
    (hj : j ≤ n) : (trace h labels start n).take j = trace h labels start j := by
  induction n with
  | zero =>
    have he : j = 0 := by omega
    subst j
    rfl
  | succ n ih =>
    by_cases he : j = n+1
    · subst j; simp
    · have hjn : j ≤ n := by omega
      rw [trace, List.take_append_of_le_length (by simpa using hjn), ih hjn]

private theorem trace_fold (h : ℕ → LowerPair) (labels : ℕ → LowerLabel) (start n : ℕ) (flip : Bool)
    (hc : ∀ j < n, h (start+j+1) = lowerChild (h (start+j)) (labels (start+j))) :
    (trace h labels start n).foldl (fun s step =>
      (lowerHistoryRawStep s.1 s.2 step.1, if step.2 then !s.2 else s.2))
      (lowerHistoryOrient (lowerPhysicalPath h start) flip, wideAt h start flip) =
    (lowerHistoryOrient (lowerPhysicalPath h (start+n)) flip, wideAt h (start+n) flip) := by
  induction n with
  | zero => simp [trace]
  | succ n ih =>
    rw [trace, List.foldl_append, ih (fun j hj => hc j (by omega))]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [← physical_step h (start+n) (labels (start+n)) flip (hc n (by omega)),
      ← wide_next]
    rfl

private theorem replay_of_trace (h : ℕ → LowerPair) (labels : ℕ → LowerLabel) (start n : ℕ)
    (base : LowerPair) (p : LowerHistoryPath) (flip : Bool)
    (hs : p.steps = trace h labels start n)
    (hentry : lowerHistoryRawStep base false p.entry =
      lowerHistoryOrient (lowerPhysicalPath h start) flip)
    (hw : p.initialWider = wideAt h start flip)
    (hc : ∀ j < n, h (start+j+1) = lowerChild (h (start+j)) (labels (start+j)))
    (j : ℕ) (hj : j ≤ n) :
    lowerHistoryReplay base p j =
      (lowerHistoryOrient (lowerPhysicalPath h (start+j)) flip, wideAt h (start+j) flip) := by
  unfold lowerHistoryReplay
  rw [hs, trace_take h labels start n j hj, hentry, hw]
  exact trace_fold h labels start j flip (fun i hi => hc i (by omega))

private theorem realizes_of_trace (h : ℕ → LowerPair) (labels : ℕ → LowerLabel) (start n : ℕ)
    (base : LowerPair) (p : LowerHistoryPath) (flip : Bool)
    (hs : p.steps = trace h labels start n)
    (hctx : lowerHistorySuffixContext base.1 p.context)
    (hb : if p.catalog = .initial then lowerEnds base.2 [3,1,3]
      else lowerEnds base.2 [3,1] ∧ ¬ lowerEnds base.2 [3,1,3,1])
    (hp : base.1.length % 2 = base.2.length % 2)
    (hentry : lowerHistoryRawStep base false p.entry =
      lowerHistoryOrient (lowerPhysicalPath h start) flip)
    (hw : p.initialWider = wideAt h start flip)
    (hc : ∀ j < n, h (start+j+1) = lowerChild (h (start+j)) (labels (start+j))) :
    lowerHistoryRealizes h start base flip p := by
  refine ⟨hctx, hb, hp, ?_⟩
  intro j hj
  have hjn : j ≤ n := by simpa [hs] using hj
  rw [replay_of_trace h labels start n base p flip hs hentry hw hc j hjn]
  exact ⟨rfl, compatible_physical h (start+j) flip, normalize_physical h (start+j) flip⟩

end GenericDesc16

-- Source: agents.origins16.window16.BirthShape

set_option maxHeartbeats 1000000

open Freiman

abbrev noP (w : List ℕ+) : Prop := ¬ (([3,1,3,1,3] : List ℕ+) <:+: w)

private theorem split5 (u v : List ℕ+) (h : u ++ v = [3,1,3,1,3]) :
    u = [] ∨ v = [] ∨ (u = [3] ∧ v = [1,3,1,3]) ∨ (u = [3,1] ∧ v = [3,1,3]) ∨
    (u = [3,1,3] ∧ v = [1,3]) ∨ (u = [3,1,3,1] ∧ v = [3]) := by
  match u with
  | [] => exact Or.inl rfl
  | [a] => simp at h; obtain ⟨h1, h2⟩ := h; subst h1; subst h2; simp
  | [a,b] => simp at h; obtain ⟨h1, h2, h3⟩ := h; subst h1; subst h2; subst h3; simp
  | [a,b,c] => simp at h; obtain ⟨h1, h2, h3, h4⟩ := h
               subst h1; subst h2; subst h3; subst h4; simp
  | [a,b,c,d] => simp at h; obtain ⟨h1, h2, h3, h4, h5⟩ := h
                 subst h1; subst h2; subst h3; subst h4; subst h5; simp
  | [a,b,c,d,e] => simp at h; exact Or.inr (Or.inl h.2.2.2.2.2)
  | a::b::c::d::e::f::u' => exfalso; simp at h

private theorem cat (A B : List ℕ+) (hA : noP A) (hB : noP B)
    (h1 : ¬ (([3]:List ℕ+) <:+ A ∧ ([1,3,1,3]:List ℕ+) <+: B))
    (h2 : ¬ (([3,1]:List ℕ+) <:+ A ∧ ([3,1,3]:List ℕ+) <+: B))
    (h3 : ¬ (([3,1,3]:List ℕ+) <:+ A ∧ ([1,3]:List ℕ+) <+: B))
    (h4 : ¬ (([3,1,3,1]:List ℕ+) <:+ A ∧ ([3]:List ℕ+) <+: B)) :
    noP (A ++ B) := by
  rintro ⟨s, t, hst⟩
  have hst' : s ++ (([3,1,3,1,3]:List ℕ+) ++ t) = A ++ B := by
    rw [← hst]; simp [List.append_assoc]
  rcases List.append_eq_append_iff.mp hst' with ⟨a', ha1, ha2⟩ | ⟨c', hc1, hc2⟩
  · rcases List.append_eq_append_iff.mp ha2 with ⟨x, hx1, hx2⟩ | ⟨y, hy1, hy2⟩
    · exact hA ⟨s, x, by rw [ha1, hx1]; simp [List.append_assoc]⟩
    · rcases split5 a' y hy1.symm with h | h | ⟨e1,e2⟩ | ⟨e1,e2⟩ | ⟨e1,e2⟩ | ⟨e1,e2⟩
      · subst h
        simp only [List.nil_append] at hy1
        exact hB ⟨[], t, by simp [hy2, ← hy1]⟩
      · subst h
        simp only [List.append_nil] at hy1
        exact hA ⟨s, [], by simp [ha1, ← hy1]⟩
      · exact h1 ⟨⟨s, by rw [ha1, e1]⟩, ⟨t, by rw [hy2, e2]⟩⟩
      · exact h2 ⟨⟨s, by rw [ha1, e1]⟩, ⟨t, by rw [hy2, e2]⟩⟩
      · exact h3 ⟨⟨s, by rw [ha1, e1]⟩, ⟨t, by rw [hy2, e2]⟩⟩
      · exact h4 ⟨⟨s, by rw [ha1, e1]⟩, ⟨t, by rw [hy2, e2]⟩⟩
  · exact hB ⟨c', t, by rw [hc2, List.append_assoc]⟩

private theorem suf_of_suf_app (l m a : List ℕ+) (h : l <:+ a ++ m) (hlen : l.length ≤ m.length) :
    l <:+ m := by
  rcases List.suffix_or_suffix_of_suffix h (List.suffix_append a m) with h' | h'
  · exact h'
  · have := h'.eq_of_length (le_antisymm h'.length_le hlen)
    rw [this]

private theorem noP_rev (w : List ℕ+) (h : noP w) : noP w.reverse := by
  intro hh
  apply h
  have : (([3,1,3,1,3] : List ℕ+)).reverse <:+: w.reverse := by simpa using hh
  exact List.reverse_infix.mp this

private theorem no1_noP (w : List ℕ+) (h : (1:ℕ+) ∉ w) : noP w := fun hh => h (hh.subset (by decide))

private theorem no1_nsuf (u w : List ℕ+) (h1 : (1:ℕ+) ∈ u) (h2 : (1:ℕ+) ∉ w) : ¬ (u <:+ w) :=
  fun hh => h2 (hh.subset h1)

private theorem no1rep (m : ℕ) : (1:ℕ+) ∉ List.replicate m (3:ℕ+) := by
  intro h; exact absurd (List.eq_of_mem_replicate h) (by decide)

private theorem admis2 (U V : List ℕ+) (hU : noP U) (hV : noP V) :
    ¬ (([3,1,3,1,3] : List ℕ+)).IsInfix (U.reverse ++ [4] ++ V) := by
  have h4V : noP ([(4:ℕ+)] ++ V) :=
    cat _ _ (by decide) hV
      (fun hh => absurd hh.1 (by decide)) (fun hh => absurd hh.1 (by decide))
      (fun hh => absurd hh.1 (by decide)) (fun hh => absurd hh.1 (by decide))
  have : noP (U.reverse ++ ([(4:ℕ+)] ++ V)) :=
    cat _ _ (noP_rev U hU) h4V
      (fun hh => absurd hh.2 (by intro hp; obtain ⟨t, ht⟩ := hp; simp at ht))
      (fun hh => absurd hh.2 (by intro hp; obtain ⟨t, ht⟩ := hp; simp at ht))
      (fun hh => absurd hh.2 (by intro hp; obtain ⟨t, ht⟩ := hp; simp at ht))
      (fun hh => absurd hh.2 (by intro hp; obtain ⟨t, ht⟩ := hp; simp at ht))
  intro hc
  exact this (by rw [List.append_assoc] at hc; exact hc)
-- ==================== WORD MACHINERY ====================
private theorem no1_npre (u w : List ℕ+) (h1 : (1:ℕ+) ∈ u) (h2 : (1:ℕ+) ∉ w) : ¬ (u <+: w) :=
  fun hh => h2 (hh.subset h1)

private theorem sufSmall : ([3,1]:List ℕ+) <:+ ([3,1,3,1]:List ℕ+) := ⟨[3,1], rfl⟩

private theorem lstar_of_l (p : LowerPair) (h : ¬ lowerL p) : ¬ lowerLStar p :=
  fun hs => h (List.IsSuffix.trans sufSmall hs)

private theorem rstar_of_r (p : LowerPair) (h : ¬ lowerR p) : ¬ lowerRStar p :=
  fun hs => h (List.IsSuffix.trans sufSmall hs)

abbrev LabDec (l : LowerLabel) : Prop :=
  (∀ d ∈ l.1, (d:ℕ) ≤ 3) ∧ (∀ d ∈ l.2, (d:ℕ) ≤ 3) ∧ 0 < l.1.length + l.2.length ∧
  noP l.1 ∧ noP l.2 ∧
  ¬ (([3,1]:List ℕ+) <:+ l.1) ∧ ¬ (([3,1,3]:List ℕ+) <:+ l.1) ∧ ¬ (([3,1,3,1]:List ℕ+) <:+ l.1) ∧
  ¬ (([1,3,1,3]:List ℕ+) <+: l.2) ∧ ¬ (([3,1,3]:List ℕ+) <+: l.2) ∧ ¬ (([1,3]:List ℕ+) <+: l.2) ∧
  ¬ (([3,1,3]:List ℕ+) <+: l.1) ∧ ¬ (([3,1,3]:List ℕ+) <:+ l.2) ∧
  l.1 ≠ ([3,1]:List ℕ+) ∧ l.2 ≠ ([1,3]:List ℕ+)

abbrev LabGuard (p : LowerPair) (l : LowerLabel) : Prop :=
  ((([3]:List ℕ+) <:+ l.1) → ¬ lowerLStar p) ∧
  ((([3]:List ℕ+) <+: l.2) → ¬ lowerRStar p) ∧
  (l.1 = ([3]:List ℕ+) → ¬ lowerL p) ∧
  (l.2 = ([3]:List ℕ+) → l = (([2]:List ℕ+),([3]:List ℕ+)) ∨ ¬ lowerR p)

private theorem earlyShape (p : LowerPair) (hNL : ¬ lowerL p) (hNRS : ¬ lowerRStar p) :
    ∀ l ∈ lowerEarlyList p, LabDec l ∧ LabGuard p l := by
  intro l hm
  unfold lowerEarlyList at hm
  split_ifs at hm <;> fin_cases hm <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))

private theorem lateShape (p : LowerPair) (hNLS : ¬ lowerLStar p) :
    ∀ l ∈ lowerLateCandidates, LabDec l ∧ LabGuard p l := by
  intro l hm
  unfold lowerLateCandidates at hm
  fin_cases hm <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))

private theorem lateMem (p : LowerPair) (l : LowerLabel) (hm : l ∈ lowerLateList p) :
    l ∈ lowerLateCandidates := by
  unfold lowerLateList at hm
  split_ifs at hm with hex
  · exact ((Classical.choose_spec hex).1 l hm).1
  · exact absurd hm (by simp)

private theorem mixShape (p : LowerPair) (l : LowerLabel) (hm : l ∈ lowerMixedList p) :
    LabDec l ∧ LabGuard p l := by
  unfold lowerMixedList at hm
  split_ifs at hm <;> fin_cases hm <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))

private theorem earlyWrap (p : LowerPair) (l : LowerLabel) (hNL : ¬ lowerL p) (hNRS : ¬ lowerRStar p)
    (hm : l ∈ lowerEarlyList p) : LabDec l ∧ LabGuard p l := earlyShape p hNL hNRS l hm

private theorem lateWrap (p : LowerPair) (l : LowerLabel) (hNLS : ¬ lowerLStar p)
    (hm : l ∈ lowerLateList p) : LabDec l ∧ LabGuard p l := lateShape p hNLS l (lateMem p l hm)

private theorem eqShape (p : LowerPair) (l : LowerLabel) (hm : l ∈ lowerEqualList p) :
    LabDec l ∧ LabGuard p l := by
  unfold lowerEqualList at hm
  split_ifs at hm
  all_goals (try (simp only [*, List.append_nil, List.nil_append] at hm))
  · fin_cases hm <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
  · fin_cases hm <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
  · fin_cases hm <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
  · fin_cases hm <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
  · fin_cases hm <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
  · rw [List.mem_append, List.mem_append] at hm
    rcases hm with (h | h) | h
    · fin_cases h <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
    · exact earlyWrap p l (by assumption) (by assumption) h
    · fin_cases h <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
  · fin_cases hm <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
  · rw [List.mem_append] at hm
    rcases hm with h | h
    · fin_cases h <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
    · exact lateWrap p l (by assumption) h
  · rw [List.mem_append, List.mem_append] at hm
    rcases hm with (h | h) | h
    · fin_cases h <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
    · exact lateWrap p l (by assumption) h
    · fin_cases h <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
  · fin_cases hm <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
  · fin_cases hm <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
  · fin_cases hm <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
  · fin_cases hm <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
  · fin_cases hm <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
  · fin_cases hm <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
  · fin_cases hm <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
  · rw [List.mem_append, List.mem_append] at hm
    rcases hm with (h | h) | h
    · fin_cases h <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
    · exact earlyWrap p l (by assumption) (by assumption) h
    · fin_cases h <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
  · fin_cases hm <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
  · rw [List.mem_append] at hm
    rcases hm with h | h
    · fin_cases h <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
    · exact lateWrap p l (by assumption) h
  · rw [List.mem_append, List.mem_append] at hm
    rcases hm with (h | h) | h
    · fin_cases h <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
    · exact lateWrap p l (by assumption) h
    · fin_cases h <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
  · fin_cases hm <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))
  · fin_cases hm <;> (refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> first | (intro hc; apply absurd hc; decide) | (intro _; exact Or.inl rfl) | (intro _; assumption) | (intro _; apply lstar_of_l; assumption) | (intro _; apply rstar_of_r; assumption) | (intro _; apply Or.inr; assumption))

private theorem labRun (k : ℕ) (hk : 0 < k) :
    LabDec ((List.replicate k (3:ℕ+)), (List.replicate k (3:ℕ+))) := by
  have hd : ∀ d ∈ List.replicate k (3:ℕ+), (d:ℕ) ≤ 3 := by
    intro d hd; rw [List.eq_of_mem_replicate hd]; decide
  have hlen : (List.replicate k (3:ℕ+)).length = k := List.length_replicate
  refine ⟨hd, hd, by simp only [hlen]; omega, no1_noP _ (no1rep k), no1_noP _ (no1rep k),
    no1_nsuf _ _ (by decide) (no1rep k), no1_nsuf _ _ (by decide) (no1rep k),
    no1_nsuf _ _ (by decide) (no1rep k), no1_npre _ _ (by decide) (no1rep k),
    no1_npre _ _ (by decide) (no1rep k), no1_npre _ _ (by decide) (no1rep k),
    no1_npre _ _ (by decide) (no1rep k), no1_nsuf _ _ (by decide) (no1rep k), ?_, ?_⟩
  · intro hc
    refine no1rep k ?_
    rw [show List.replicate k (3:ℕ+) = [3,1] from hc]
    decide
  · intro hc
    refine no1rep k ?_
    rw [show List.replicate k (3:ℕ+) = [1,3] from hc]
    decide

private theorem runGuard (p : LowerPair) (k : ℕ) (hr : lowerRunOffered p) :
    LabGuard p ((List.replicate k (3:ℕ+)), (List.replicate k (3:ℕ+))) := by
  obtain ⟨-, -, hNL, hNR, -⟩ := hr
  exact ⟨fun _ => lstar_of_l p hNL, fun _ => rstar_of_r p hNR, fun _ => hNL, fun _ => Or.inr hNR⟩

private theorem offShape (p : LowerPair) (l : LowerLabel) (ho : lowerOffered p l) :
    LabDec l ∧ LabGuard p l := by
  classical
  unfold lowerOffered at ho
  rcases ho with hm | ⟨hr, k, hk, rfl⟩
  · by_cases hmix : lowerMixed p
    · rw [if_pos hmix] at hm; exact mixShape p l hm
    · rw [if_neg hmix] at hm; exact eqShape p l hm
  · exact ⟨labRun k hk, runGuard p k hr⟩

-- ==================== structural helpers ====================
private theorem normLenSum (p : LowerPair) :
    (lowerNormalize p).1.length + (lowerNormalize p).2.length = p.1.length + p.2.length := by
  unfold lowerNormalize
  split
  · rfl
  · exact Nat.add_comm _ _

private theorem coreSwap (c : LowerPair) (hc : c ∈ lowerCores) : c.swap ∈ lowerCores := by
  revert hc
  unfold lowerCores lowerBaseCores
  intro hc
  fin_cases hc <;> decide

private theorem extSwap (c p : LowerPair) (h : lowerExtends c p) : lowerExtends c.swap p.swap := by
  obtain ⟨u, v, he, hu, hv⟩ := h
  exact ⟨v, u, by rw [he]; rfl, hv, hu⟩

private theorem extApp (c p : LowerPair) (u v : List ℕ+) (h : lowerExtends c p)
    (hu : ∀ d ∈ u, (d:ℕ) ≤ 3) (hv : ∀ d ∈ v, (d:ℕ) ≤ 3) :
    lowerExtends c (p.1 ++ u, p.2 ++ v) := by
  obtain ⟨u0, v0, he, hu0, hv0⟩ := h
  refine ⟨u0 ++ u, v0 ++ v, ?_, ?_, ?_⟩
  · rw [he]; simp [List.append_assoc]
  · intro d hd
    rcases List.mem_append.mp hd with hh | hh
    · exact hu0 d hh
    · exact hu d hh
  · intro d hd
    rcases List.mem_append.mp hd with hh | hh
    · exact hv0 d hh
    · exact hv d hh

private theorem noPparts (A B : List ℕ+)
    (h : ¬ (([3,1,3,1,3]:List ℕ+)).IsInfix (A ++ [4] ++ B)) : noP A ∧ noP B := by
  constructor
  · intro hc; exact h (hc.trans ⟨[], [4] ++ B, by simp⟩)
  · intro hc; exact h (hc.trans ⟨A ++ [4], [], by simp⟩)

private theorem lstarPre (w : List ℕ+) (h : ([1,3,1,3]:List ℕ+) <+: w.reverse) :
    ([3,1,3,1]:List ℕ+) <:+ w :=
  List.reverse_prefix.mp (show ([3,1,3,1]:List ℕ+).reverse <+: w.reverse from h)

private theorem lPre (w : List ℕ+) (h : ([1,3]:List ℕ+) <+: w.reverse) : ([3,1]:List ℕ+) <:+ w :=
  List.reverse_prefix.mp (show ([3,1]:List ℕ+).reverse <+: w.reverse from h)

private theorem split3 (u v : List ℕ+) (h : u ++ v = [3,1,3]) :
    u = [] ∨ (u = [3] ∧ v = [1,3]) ∨ (u = [3,1] ∧ v = [3]) ∨ u = [3,1,3] := by
  match u with
  | [] => exact Or.inl rfl
  | [a] => simp at h; obtain ⟨h1, h2⟩ := h; subst h1; subst h2; simp
  | [a,b] => simp at h; obtain ⟨h1, h2, h3⟩ := h; subst h1; subst h2; subst h3; simp
  | [a,b,c] =>
      simp at h; obtain ⟨h1, h2, h3, h4⟩ := h; subst h1; subst h2; subst h3; subst h4; simp
  | a::b::c::d::u' => exfalso; simp at h

private theorem pre3 (A B : List ℕ+) (h : ([3,1,3]:List ℕ+) <+: (A ++ B)) :
    (([3,1,3]:List ℕ+) <+: A) ∨ (A = [] ∧ ([3,1,3]:List ℕ+) <+: B) ∨
    (A = [3] ∧ ([1,3]:List ℕ+) <+: B) ∨ (A = [3,1] ∧ ([3]:List ℕ+) <+: B) := by
  obtain ⟨t, ht⟩ := h
  rcases List.append_eq_append_iff.mp ht with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩
  · exact Or.inl ⟨c, hc1.symm⟩
  · rcases split3 A c hc1.symm with hA | ⟨hA, hc⟩ | ⟨hA, hc⟩ | hA
    · subst hA
      simp only [List.nil_append] at hc1
      subst hc1
      exact Or.inr (Or.inl ⟨rfl, ⟨t, hc2.symm⟩⟩)
    · subst hA; subst hc
      exact Or.inr (Or.inr (Or.inl ⟨rfl, ⟨t, hc2.symm⟩⟩))
    · subst hA; subst hc
      exact Or.inr (Or.inr (Or.inr ⟨rfl, ⟨t, hc2.symm⟩⟩))
    · exact Or.inl ⟨[], by rw [hA]; simp⟩



-- Source: agents.genericdesc16.Birth
open Freiman
namespace GenericDesc16
attribute [local instance] Classical.propDecidable

private theorem child_injective (p : LowerPair) : Function.Injective (lowerChild p) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  simp only [lowerChild] at h
  injection h with h₁ h₂
  have h₁' : a.reverse = c.reverse := List.append_right_injective _ h₁
  have h₂' : b = d := List.append_right_injective _ h₂
  have h₁'' : a = c := by simpa using congrArg List.reverse h₁'
  exact Prod.ext h₁'' h₂'

private theorem offered_birth (t : ℝ) (h : ℕ → LowerPair) (n m : ℕ)
    (hh : lowerHistory t h n) (hm0 : 0 < m) (hmn : m ≤ n)
    (hbirth : h m = lowerChild (h (m-1)) ([2],[3])) :
    lowerOffered (h (m-1)) ([2],[3]) := by
  obtain ⟨l, hl, _, he⟩ := hh.2.2 (m-1) (by omega)
  have heq : m-1+1=m := by omega
  rw [heq, hbirth] at he
  have hlab := child_injective (h (m-1)) he
  simpa [← hlab] using hl

private theorem offered_birth_parity (p : LowerPair) (ho : lowerOffered p ([2],[3])) :
    ¬ lowerMixed p := by
  intro hp
  rcases ho with ho | ⟨hr, k, hk, he⟩
  · simp only [if_pos hp] at ho
    unfold lowerMixedList at ho
    split_ifs at ho <;> simp_all
  · exact hr.1 hp

private theorem normalized_birth_parity (p : LowerPair) (ho : lowerOffered p ([2],[3])) :
    (lowerNormalize p).1.length % 2 = (lowerNormalize p).2.length % 2 := by
  have hp := not_not.mp (offered_birth_parity p ho)
  unfold lowerNormalize
  split_ifs <;> simp_all

private theorem offered_birth_not_rstar (p : LowerPair) (ho : lowerOffered p ([2],[3])) :
    ¬ lowerRStar p := by
  exact (offShape p ([2],[3]) ho).2.2.1 (by decide)

private theorem birth_left_unmarked (p : LowerPair) :
    ¬ lowerEnds (lowerChild p ([2],[3])).1 [3,1,3] := by
  intro hh
  change [3,1] ++ [3] <:+ (lowerNormalize p).1 ++ [2] at hh
  have hx := (List.suffix_append_inj_of_length_eq (l₁ := [3,1])
    (l₂ := (lowerNormalize p).1) (s₁ := [3]) (s₂ := [2]) (by rfl)).mp hh
  norm_num at hx

private theorem birth_marked_side (h : ℕ → LowerPair) (m : ℕ) (right : Bool)
    (hc : h m = lowerChild (h (m-1)) ([2],[3]))
    (hm : lowerEnds (lowerSide (lowerPhysicalPath h m) right) [3,1,3]) :
    right = !(lowerOrientation h m) := by
  have hn := birth_left_unmarked (h (m-1))
  cases ho : lowerOrientation h m <;> cases right <;>
    simp_all [lowerPhysicalPath, lowerSide]

private theorem birth_base_suffix (h : ℕ → LowerPair) (m : ℕ) (right : Bool)
    (hc : h m = lowerChild (h (m-1)) ([2],[3]))
    (hm : lowerEnds (lowerSide (lowerPhysicalPath h m) right) [3,1,3]) :
    lowerEnds (lowerNormalize (h (m-1))).2 [3,1] := by
  have hr := birth_marked_side h m right hc hm
  have hh : lowerEnds (h m).2 [3,1,3] := by
    cases ho : lowerOrientation h m <;> simp_all [lowerPhysicalPath, lowerSide]
  rw [hc] at hh
  change [3,1] ++ [3] <:+ (lowerNormalize (h (m-1))).2 ++ [3] at hh
  exact List.suffix_append_self_iff.mp hh

private theorem birth_orient_before (h : ℕ → LowerPair) (m : ℕ) (hm : 0 < m) :
    lowerHistoryOrient (lowerPhysicalPath h (m-1)) (lowerOrientation h m) =
      lowerNormalize (h (m-1)) := by
  have he : m-1+1=m := by omega
  have hw : lowerOrientation h m = wideAt h (m-1) false := by
    rw [← he]
    simp [lowerOrientation, wideAt]
  rw [hw]
  simpa [lowerHistoryOrient] using (normalize_physical h (m-1) false).symm

private theorem birth_orient_at (h : ℕ → LowerPair) (m : ℕ) :
    lowerHistoryOrient (lowerPhysicalPath h m) (lowerOrientation h m) = h m := by
  cases ho : lowerOrientation h m <;> simp [lowerHistoryOrient, lowerPhysicalPath, ho]

private theorem birth_entry (h : ℕ → LowerPair) (m : ℕ)
    (hc : h m = lowerChild (h (m-1)) ([2],[3])) :
    lowerHistoryRawStep (lowerNormalize (h (m-1))) false ([2],[3]) =
      lowerHistoryOrient (lowerPhysicalPath h m) (lowerOrientation h m) := by
  rw [birth_orient_at, hc]
  rfl

end GenericDesc16

-- Source: agents.genericdesc16.Context
open Freiman
namespace GenericDesc16
attribute [local instance] Classical.propDecidable
private def smallEnd (w : List ℕ+) : Prop :=
  lowerEnds w [1] ∨ lowerEnds w [2] ∨ lowerEnds w [3]

private theorem smallEnd_of_last (w : List ℕ+) (hn : w ≠ [])
    (hl : ((w.getLast hn : ℕ)) ≤ 3) : smallEnd w := by
  have hp : 0 < (w.getLast hn : ℕ) := PNat.pos _
  have hd : (w.getLast hn : ℕ) = 1 ∨ (w.getLast hn : ℕ) = 2 ∨
      (w.getLast hn : ℕ) = 3 := by omega
  have hs := List.dropLast_append_getLast hn
  rcases hd with h | h | h
  · have he : w.getLast hn = 1 := by exact_mod_cast h
    left
    exact ⟨w.dropLast, by simpa [he] using hs⟩
  · have he : w.getLast hn = 2 := by exact_mod_cast h
    right; left
    exact ⟨w.dropLast, by simpa [he] using hs⟩
  · have he : w.getLast hn = 3 := by exact_mod_cast h
    right; right
    exact ⟨w.dropLast, by simpa [he] using hs⟩

private theorem append_smallEnd (w u : List ℕ+) (hw : smallEnd w)
    (hu : ∀ d ∈ u, (d : ℕ) ≤ 3) : smallEnd (w ++ u) := by
  induction u generalizing w with
  | nil => simpa using hw
  | cons a u ih =>
      rw [show w ++ a :: u = (w ++ [a]) ++ u by simp]
      apply ih (w := w ++ [a])
      · have ha := hu a (by simp)
        have hp : 0 < (a : ℕ) := PNat.pos a
        have : (a : ℕ) = 1 ∨ (a : ℕ) = 2 ∨ (a : ℕ) = 3 := by omega
        rcases this with h | h | h
        · have ha1 : a = 1 := by exact_mod_cast h
          left; exact ⟨w, by simp [ha1]⟩
        · have ha2 : a = 2 := by exact_mod_cast h
          right; left; exact ⟨w, by simp [ha2]⟩
        · have ha3 : a = 3 := by exact_mod_cast h
          right; right; exact ⟨w, by simp [ha3]⟩
      · intro d hd
        exact hu d (by simp [hd])

private theorem admissible_smallEnds (p : LowerPair) (ha : lowerAdmissible p) :
    smallEnd p.1 ∧ smallEnd p.2 := by
  rcases ha.1 with ⟨c,hc,u,v,rfl,hu,hv⟩
  have hbase : smallEnd c.1 ∧ smallEnd c.2 := by
    simp only [lowerCores,lowerBaseCores,List.mem_append,List.mem_cons,List.mem_map,
      List.not_mem_nil,or_false] at hc
    rcases hc with hc | ⟨d,hd,rfl⟩
    · rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> constructor <;> apply smallEnd_of_last <;> simp
    · rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> constructor <;> apply smallEnd_of_last <;> simp
  exact ⟨append_smallEnd _ _ hbase.1 hu,append_smallEnd _ _ hbase.2 hv⟩


private theorem context_of_smallEnd (w : List ℕ+) (hs : smallEnd w) :
    ∃ ctx ∈ lowerHistoryContextWords, lowerHistorySuffixContext w ctx := by
  by_cases h31 : lowerEnds w [3,1]
  · refine ⟨[3,1], by decide, ?_⟩
    rcases h31 with ⟨pre, rfl⟩
    simp [lowerHistorySuffixContext, lowerEnds, ← List.reverse_prefix]
  · rcases hs with h1 | h2 | h3
    · refine ⟨[1], by decide, h1, ?_, ?_⟩
      · rcases h1 with ⟨pre,rfl⟩
        simp [lowerEnds, ← List.reverse_prefix]
      · exact iff_of_false h31 (by simp [lowerEnds, ← List.reverse_prefix])
    · refine ⟨[2], by decide, ?_⟩
      rcases h2 with ⟨pre,rfl⟩
      simp [lowerHistorySuffixContext, lowerEnds, ← List.reverse_prefix]
    · refine ⟨[3], by decide, ?_⟩
      rcases h3 with ⟨pre,rfl⟩
      simp [lowerHistorySuffixContext, lowerEnds, ← List.reverse_prefix]

private theorem admissible_context (p : LowerPair) (ha : lowerAdmissible p) :
    ∃ ctx ∈ lowerHistoryContextWords,
      lowerHistorySuffixContext (lowerNormalize p).1 ctx := by
  have hs := admissible_smallEnds p ha
  unfold lowerNormalize
  split_ifs
  · exact context_of_smallEnd p.1 hs.1
  · exact context_of_smallEnd p.2 hs.2

end GenericDesc16

-- Source: agents.genericdesc16.Span
open Freiman
namespace GenericDesc16
attribute [local instance] Classical.propDecidable

private theorem actual_labels (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n) :
    ∃ labels : ℕ → LowerLabel, ∀ j < n,
      lowerOffered (h j) (labels j) ∧ lowerPriority t (h j) (labels j) ∧
      h (j+1) = lowerChild (h j) (labels j) := by
  have hx : ∀ j : ℕ, ∃ l : LowerLabel, j < n →
      lowerOffered (h j) l ∧ lowerPriority t (h j) l ∧ h (j+1) = lowerChild (h j) l := by
    intro j
    by_cases hj : j < n
    · obtain ⟨l,hl⟩ := hh.2.2 j hj
      exact ⟨l,fun _ => hl⟩
    · exact ⟨([],[]),fun hjn => (hj hjn).elim⟩
  choose labels hl using hx
  exact ⟨labels,hl⟩

private theorem orient_side (p : LowerPair) (flip : Bool) :
    (lowerHistoryOrient p flip).2 = lowerSide p (!flip) := by
  cases flip <;> rfl

private theorem generic_span_data (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (right : Bool)
    (hh : lowerHistory t h n) (hm : lowerGenericMarked h n right) :
    ∃ m ctx,
      0 < m ∧ m ≤ n ∧ n-m ≤ 7 ∧
      ctx ∈ lowerHistoryContextWords ∧
      lowerHistorySuffixContext (lowerNormalize (h (m-1))).1 ctx ∧
      lowerEnds (lowerNormalize (h (m-1))).2 [3,1] ∧
      ¬ lowerEnds (lowerNormalize (h (m-1))).2 [3,1,3,1] ∧
      (lowerNormalize (h (m-1))).1.length % 2 =
        (lowerNormalize (h (m-1))).2.length % 2 ∧
      h m = lowerChild (h (m-1)) ([2],[3]) ∧
      right = !(lowerOrientation h m) ∧
      ∀ j, m ≤ j → j ≤ n →
        lowerEnds (lowerHistoryOrient (lowerPhysicalPath h j) (lowerOrientation h m)).2 [3,1,3] ∨
        lowerEnds (lowerHistoryOrient (lowerPhysicalPath h j) (lowerOrientation h m)).2 [3,1,3,1] := by
  obtain ⟨m,hm0,hmn,hlen,hbirth,hmark,hpres⟩ := hm
  have hoff := offered_birth t h n m hh hm0 hmn hbirth
  have hctx := admissible_context (h (m-1)) (hh.2.1 (m-1) (by omega)).1
  obtain ⟨ctx,hctx,hctxfull⟩ := hctx
  have hright := birth_marked_side h m right hbirth hmark
  refine ⟨m,ctx,hm0,hmn,hlen,hctx,hctxfull,
    birth_base_suffix h m right hbirth hmark,
    offered_birth_not_rstar _ hoff, normalized_birth_parity _ hoff,
    hbirth,hright,?_⟩
  intro j hj hjn
  simpa only [orient_side, ← hright] using hpres j hj hjn

end GenericDesc16

-- Source: agents.genericdesc16.StepBase
open Freiman
set_option maxHeartbeats 0
set_option linter.all false
namespace GenericLegal16
attribute [local instance] Classical.propDecidable
abbrev RelSix (l : LowerLabel) : Prop :=
  (l.1.reverse, l.2) = ([1],[]) ∨ (l.1.reverse,l.2) = ([2],[]) ∨
  (l.1.reverse,l.2) = ([3],[]) ∨ (l.1.reverse,l.2) = ([],[1]) ∨
  (l.1.reverse,l.2) = ([2],[1]) ∨ (l.1.reverse,l.2) = ([3],[1])
abbrev HasMark (w : List ℕ+) : Prop :=
  lowerEnds w [3,1,3] ∨ lowerEnds w [3,1,3,1]
abbrev SixDec (p : LowerPair) (l : LowerLabel) : Prop :=
  (HasMark (lowerNormalize p).1 → (l.1.reverse = [] ∨ l.1.reverse = [1]) → RelSix l ∧ (l.1 = [] → lowerMixed p)) ∧
  (HasMark (lowerNormalize p).2 → (l.2 = [] ∨ l.2 = [1]) →
    RelSix l ∧ (l.1 = [] → lowerMixed p))

private theorem sx_lstar_of_l (p : LowerPair) (h : ¬ lowerL p) : ¬ lowerLStar p := by
  intro hs
  exact h ((show ([3,1] : List ℕ+).IsSuffix [3,1,3,1] by decide).trans hs)
private theorem sx_rstar_of_r (p : LowerPair) (h : ¬ lowerR p) : ¬ lowerRStar p := by
  intro hs
  exact h ((show ([3,1] : List ℕ+).IsSuffix [3,1,3,1] by decide).trans hs)
private theorem sx_earlyShape (p : LowerPair) (hNL : ¬ lowerL p) (hNRS : ¬ lowerRStar p) :
    ∀ l ∈ lowerEarlyList p, SixDec p l := by
  intro l hm
  unfold lowerEarlyList at hm
  split_ifs at hm <;> fin_cases hm <;> (simp_all [SixDec, RelSix])

private theorem sx_lateShape (p : LowerPair) (hNLS : ¬ lowerLStar p) :
    ∀ l ∈ lowerLateCandidates, SixDec p l := by
  intro l hm
  unfold lowerLateCandidates at hm
  fin_cases hm <;> (simp_all [SixDec, RelSix])

private theorem sx_lateMem (p : LowerPair) (l : LowerLabel) (hm : l ∈ lowerLateList p) :
    l ∈ lowerLateCandidates := by
  unfold lowerLateList at hm
  split_ifs at hm with hex
  · exact ((Classical.choose_spec hex).1 l hm).1
  · exact absurd hm (by simp)

private theorem sx_mixShape (p : LowerPair) (l : LowerLabel) (hp : lowerMixed p) (hm : l ∈ lowerMixedList p) :
    SixDec p l := by
  unfold lowerMixedList at hm
  split_ifs at hm <;> fin_cases hm <;> (simp_all [SixDec, RelSix])

private theorem sx_earlyWrap (p : LowerPair) (l : LowerLabel) (hNL : ¬ lowerL p) (hNRS : ¬ lowerRStar p)
    (hm : l ∈ lowerEarlyList p) : SixDec p l := sx_earlyShape p hNL hNRS l hm

private theorem sx_lateWrap (p : LowerPair) (l : LowerLabel) (hNLS : ¬ lowerLStar p)
    (hm : l ∈ lowerLateList p) : SixDec p l := sx_lateShape p hNLS l (sx_lateMem p l hm)

private theorem sx_eqShape (p : LowerPair) (l : LowerLabel) (hm : l ∈ lowerEqualList p) :
    SixDec p l := by
  unfold lowerEqualList at hm
  split_ifs at hm
  all_goals (try (simp only [*, List.append_nil, List.nil_append] at hm))
  · fin_cases hm <;> (simp_all [SixDec, RelSix])
  · fin_cases hm <;> (simp_all [SixDec, RelSix])
  · fin_cases hm <;> (simp_all [SixDec, RelSix])
  · fin_cases hm <;> (simp_all [SixDec, RelSix])
  · fin_cases hm <;> (simp_all [SixDec, RelSix])
  · rw [List.mem_append, List.mem_append] at hm
    rcases hm with (h | h) | h
    · fin_cases h <;> (simp_all [SixDec, RelSix])
    · exact sx_earlyWrap p l (by assumption) (by assumption) h
    · fin_cases h <;> (simp_all [SixDec, RelSix])
  · fin_cases hm <;> (simp_all [SixDec, RelSix])
  · rw [List.mem_append] at hm
    rcases hm with h | h
    · fin_cases h <;> (simp_all [SixDec, RelSix])
    · exact sx_lateWrap p l (by assumption) h
  · rw [List.mem_append, List.mem_append] at hm
    rcases hm with (h | h) | h
    · fin_cases h <;> (simp_all [SixDec, RelSix])
    · exact sx_lateWrap p l (by assumption) h
    · fin_cases h <;> (simp_all [SixDec, RelSix])
  · fin_cases hm <;> (simp_all [SixDec, RelSix])
  · fin_cases hm <;> (simp_all [SixDec, RelSix])
  · fin_cases hm <;> (simp_all [SixDec, RelSix])
  · fin_cases hm <;> (simp_all [SixDec, RelSix])
  · fin_cases hm <;> (simp_all [SixDec, RelSix])
  · fin_cases hm <;> (simp_all [SixDec, RelSix])
  · fin_cases hm <;> (simp_all [SixDec, RelSix])
  · rw [List.mem_append, List.mem_append] at hm
    rcases hm with (h | h) | h
    · fin_cases h <;> (simp_all [SixDec, RelSix])
    · exact sx_earlyWrap p l (by assumption) (by assumption) h
    · fin_cases h <;> (simp_all [SixDec, RelSix])
  · fin_cases hm <;> (simp_all [SixDec, RelSix])
  · rw [List.mem_append] at hm
    rcases hm with h | h
    · fin_cases h <;> (simp_all [SixDec, RelSix])
    · exact sx_lateWrap p l (by assumption) h
  · rw [List.mem_append, List.mem_append] at hm
    rcases hm with (h | h) | h
    · fin_cases h <;> (simp_all [SixDec, RelSix])
    · exact sx_lateWrap p l (by assumption) h
    · fin_cases h <;> (simp_all [SixDec, RelSix])
  · fin_cases hm <;> (simp_all [SixDec, RelSix])
  · fin_cases hm <;> (simp_all [SixDec, RelSix])




private theorem offSix (p : LowerPair) (l : LowerLabel) (ho : lowerOffered p l) : SixDec p l := by
  classical
  unfold lowerOffered at ho
  rcases ho with hm | ⟨hr, k, hk, rfl⟩
  · by_cases hmix : lowerMixed p
    · rw [if_pos hmix] at hm; exact sx_mixShape p _ hmix hm
    · rw [if_neg hmix] at hm; exact sx_eqShape p _ hm
  · have himp : ¬ (List.replicate k (3 : ℕ+) = [] ∨
        List.replicate k (3 : ℕ+) = [1]) := by
      intro hs
      rcases hs with hs | hs
      · have he := congrArg List.length hs
        simp at he
        omega
      · have hm : (1 : ℕ+) ∈ List.replicate k (3 : ℕ+) := by rw [hs]; simp
        have he := List.eq_of_mem_replicate hm
        norm_num at he
    constructor <;> intro _ hs
    · apply False.elim (himp (by simpa using hs))
    · apply False.elim (himp hs)



abbrev sf_Marked (w : List ℕ+) (done : Bool) : Prop :=
  if done then lowerEnds w [3,1,3,1] else lowerEnds w [3,1,3]

private theorem sf_split4 (u v : List ℕ+) (h : u ++ v = [1,3,1,3]) :
    u = [] ∨ (u=[1] ∧ v=[3,1,3]) ∨ (u=[1,3] ∧ v=[1,3]) ∨
    (u=[1,3,1] ∧ v=[3]) ∨ u=[1,3,1,3] := by
  match u with
  | [] => exact Or.inl rfl
  | [a] => simp at h; obtain ⟨rfl,rfl⟩ := h; simp
  | [a,b] => simp at h; obtain ⟨rfl,rfl,rfl⟩ := h; simp
  | [a,b,c] => simp at h; obtain ⟨rfl,rfl,rfl,rfl⟩ := h; simp
  | [a,b,c,d] => simp at h; obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := h; simp
  | a::b::c::d::e::u => exfalso; simp at h

private theorem sf_pre4 (A B : List ℕ+) (h : ([1,3,1,3] : List ℕ+) <+: A++B) :
    ([1,3,1,3] : List ℕ+) <+: A ∨
    (A=[] ∧ ([1,3,1,3] : List ℕ+) <+: B) ∨
    (A=[1] ∧ ([3,1,3] : List ℕ+) <+: B) ∨
    (A=[1,3] ∧ ([1,3] : List ℕ+) <+: B) ∨
    (A=[1,3,1] ∧ ([3] : List ℕ+) <+: B) := by
  obtain ⟨z,hz⟩ := h
  rcases List.append_eq_append_iff.mp hz with ⟨c,hc1,hc2⟩ | ⟨c,hc1,hc2⟩
  · exact Or.inl ⟨c,hc1.symm⟩
  · rcases sf_split4 A c hc1.symm with hA | ⟨hA,hc⟩ | ⟨hA,hc⟩ | ⟨hA,hc⟩ | hA
    · subst A; simp only [List.nil_append] at hc1; subst c
      exact Or.inr (Or.inl ⟨rfl,⟨z,hc2.symm⟩⟩)
    · subst A; subst c; exact Or.inr (Or.inr (Or.inl ⟨rfl,⟨z,hc2.symm⟩⟩))
    · subst A; subst c; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,⟨z,hc2.symm⟩⟩)))
    · subst A; subst c; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,⟨z,hc2.symm⟩⟩)))
    · exact Or.inl ⟨[],by rw [hA]; simp⟩

private theorem sf_split3 (u v : List ℕ+) (h : u ++ v = [3,1,3]) :
    u=[] ∨ (u=[3] ∧ v=[1,3]) ∨ (u=[3,1] ∧ v=[3]) ∨ u=[3,1,3] := by
  match u with
  | [] => exact Or.inl rfl
  | [a] => simp at h; obtain ⟨rfl,rfl⟩ := h; simp
  | [a,b] => simp at h; obtain ⟨rfl,rfl,rfl⟩ := h; simp
  | [a,b,c] => simp at h; obtain ⟨rfl,rfl,rfl,rfl⟩ := h; simp
  | a::b::c::d::u => exfalso; simp at h

private theorem sf_pre3 (A B : List ℕ+) (h : ([3,1,3] : List ℕ+) <+: A++B) :
    ([3,1,3] : List ℕ+) <+: A ∨ (A=[] ∧ ([3,1,3] : List ℕ+) <+: B) ∨
    (A=[3] ∧ ([1,3] : List ℕ+) <+: B) ∨ (A=[3,1] ∧ ([3] : List ℕ+) <+: B) := by
  obtain ⟨z,hz⟩ := h
  rcases List.append_eq_append_iff.mp hz with ⟨c,hc1,hc2⟩ | ⟨c,hc1,hc2⟩
  · exact Or.inl ⟨c,hc1.symm⟩
  · rcases sf_split3 A c hc1.symm with hA | ⟨hA,hc⟩ | ⟨hA,hc⟩ | hA
    · subst A; simp only [List.nil_append] at hc1; subst c
      exact Or.inr (Or.inl ⟨rfl,⟨z,hc2.symm⟩⟩)
    · subst A; subst c; exact Or.inr (Or.inr (Or.inl ⟨rfl,⟨z,hc2.symm⟩⟩))
    · subst A; subst c; exact Or.inr (Or.inr (Or.inr ⟨rfl,⟨z,hc2.symm⟩⟩))
    · exact Or.inl ⟨[],by rw [hA]; simp⟩

private theorem sf_prefix_unique {u v w : List ℕ+} (hu : u <+: w) (hv : v <+: w)
    (hlen : u.length=v.length) : u=v := by
  have eu : w.take u.length = u := by obtain ⟨z,rfl⟩ := hu; simp
  have ev : w.take v.length = v := by obtain ⟨z,rfl⟩ := hv; simp
  rw [← eu, ← ev, hlen]

private theorem sf_marked_unique (A : List ℕ+) (d e : Bool)
    (hd : sf_Marked A d) (he : sf_Marked A e) : d=e := by
  cases d <;> cases e
  · rfl
  · have h313 : ([3,1,3] : List ℕ+) <+: A.reverse := by simpa using List.reverse_prefix.mpr hd
    have h1313 : ([1,3,1,3] : List ℕ+) <+: A.reverse := by simpa using List.reverse_prefix.mpr he
    have h131 : ([1,3,1] : List ℕ+) <+: A.reverse :=
      (show ([1,3,1] : List ℕ+) <+: [1,3,1,3] by decide).trans h1313
    exact absurd (sf_prefix_unique h313 h131 (by decide)) (by decide)
  · have h1313 : ([1,3,1,3] : List ℕ+) <+: A.reverse := by simpa using List.reverse_prefix.mpr hd
    have h131 : ([1,3,1] : List ℕ+) <+: A.reverse :=
      (show ([1,3,1] : List ℕ+) <+: [1,3,1,3] by decide).trans h1313
    have h313 : ([3,1,3] : List ℕ+) <+: A.reverse := by simpa using List.reverse_prefix.mpr he
    exact absurd (sf_prefix_unique h131 h313 (by decide)) (by decide)
  · rfl

private theorem sf_append_marked (A B : List ℕ+) (dp dc : Bool)
    (hp : sf_Marked A dp) (hc : sf_Marked (A++B) dc)
    (hn31 : ¬ lowerEnds B [3,1]) (hn131 : ¬ lowerEnds B [1,3,1])
    (hn313 : ¬ lowerEnds B [3,1,3]) (hn3131 : ¬ lowerEnds B [3,1,3,1])
    (hne13 : B ≠ [1,3])
    (had : ¬ ([3,1,3,1,3] : List ℕ+).IsInfix (A++B)) :
    (B=[] ∧ dp=dc) ∨ (dp=false ∧ dc=true ∧ B=[1]) := by
  cases dc
  · have hr : ([3,1,3] : List ℕ+) <+: B.reverse++A.reverse := by
      simpa using List.reverse_prefix.mpr hc
    rcases sf_pre3 B.reverse A.reverse hr with h | ⟨h,-⟩ | ⟨h,ha⟩ | ⟨h,ha⟩
    · exact absurd (List.reverse_prefix.mp (by simpa using h)) hn313
    · have hb0 : B=[] := by simpa using congrArg List.reverse h
      have hc' : sf_Marked A false := by simpa [hb0] using hc
      exact Or.inl ⟨hb0, sf_marked_unique A dp false hp hc'⟩
    · have hb : B=[3] := by simpa using congrArg List.reverse h
      right
      cases dp
      · have h31 : ([3,1] : List ℕ+) <+: A.reverse := by
          have h313 : ([3,1,3] : List ℕ+) <+: A.reverse := by simpa using List.reverse_prefix.mpr hp
          exact (show ([3,1] : List ℕ+) <+: [3,1,3] by decide).trans h313
        exact absurd (sf_prefix_unique ha h31 (by decide)) (by decide)
      · exfalso
        apply had
        obtain ⟨z,hz⟩ := hp
        have hs : ([3,1,3,1,3] : List ℕ+).IsSuffix (A++B) := ⟨z, by
          calc z ++ [3,1,3,1,3] = (z++[3,1,3,1])++[3] := by simp
            _ = A++B := by rw [hz,hb]⟩
        exact hs.isInfix
    · have hb : B=[1,3] := by simpa using congrArg List.reverse h
      exact absurd hb hne13
  · have hr : ([1,3,1,3] : List ℕ+) <+: B.reverse++A.reverse := by
      simpa using List.reverse_prefix.mpr hc
    rcases sf_pre4 B.reverse A.reverse hr with h | ⟨h,-⟩ | ⟨h,ha⟩ | ⟨h,-⟩ | ⟨h,-⟩
    · exact absurd (List.reverse_prefix.mp (by simpa using h)) hn3131
    · have hb0 : B=[] := by simpa using congrArg List.reverse h
      have hc' : sf_Marked A true := by simpa [hb0] using hc
      exact Or.inl ⟨hb0, sf_marked_unique A dp true hp hc'⟩
    · right
      have hb : B=[1] := by simpa using congrArg List.reverse h
      refine ⟨?_,rfl,hb⟩
      cases dp
      · rfl
      · have h1313 : ([1,3,1,3] : List ℕ+) <+: A.reverse := by
          simpa using List.reverse_prefix.mpr hp
        have h313 : ([3,1,3] : List ℕ+) <+: A.reverse := by simpa using ha
        have h131 : ([1,3,1] : List ℕ+) <+: A.reverse :=
          (show ([1,3,1] : List ℕ+) <+: [1,3,1,3] by decide).trans h1313
        exact absurd (sf_prefix_unique h131 h313 (by decide)) (by decide)
    · have hb : B=[3,1] := by simpa using congrArg List.reverse h
      exfalso; apply hn31; rw [hb]; exact ⟨[],rfl⟩
    · have hb : B=[1,3,1] := by simpa using congrArg List.reverse h
      exfalso
      apply hn131
      rw [hb]
      exact ⟨[],rfl⟩



inductive RL where | a1 | a2 | a3 | b1 | a2b1 | a3b1
  deriving DecidableEq, Repr

private def RL.all : List RL := [.a1,.a2,.a3,.b1,.a2b1,.a3b1]
private def RL.a : RL → List ℕ+
  | .a1 => [1] | .a2 => [2] | .a3 => [3] | .b1 => []
  | .a2b1 => [2] | .a3b1 => [3]
private def RL.b : RL → List ℕ+
  | .a1 | .a2 | .a3 => [] | .b1 | .a2b1 | .a3b1 => [1]

private def bitlen (w : List ℕ+) : Bool := decide (w.length % 2 = 1)

private theorem normalize_reflect (p : LowerPair) :
    lowerNormalize p = if lowerReflects p then p.swap else p := by
  rcases p with ⟨p,q⟩
  unfold lowerNormalize lowerReflects
  by_cases h : lowerWidth q ≤ lowerWidth p
  · have hn : ¬ lowerWidth p < lowerWidth q := not_lt.mpr h
    simp [h, hn]
  · have hl : lowerWidth p < lowerWidth q := lt_of_not_ge h
    simp [h, hl, Prod.swap]

private theorem physical_step (h : ℕ → LowerPair) (j : ℕ) (l : LowerLabel)
    (hc : h (j+1) = lowerChild (h j) l) :
    lowerPhysicalPath h (j+1) =
      if (lowerOrientation h j).xor (lowerReflects (h j)) then
        ((lowerPhysicalPath h j).1 ++ l.2,
         (lowerPhysicalPath h j).2 ++ l.1.reverse)
      else
        ((lowerPhysicalPath h j).1 ++ l.1.reverse,
         (lowerPhysicalPath h j).2 ++ l.2) := by
  cases ho : lowerOrientation h j <;> cases hr : lowerReflects (h j) <;>
    simp [lowerPhysicalPath, lowerOrientation, hc, lowerChild, normalize_reflect,
      ho, hr, Prod.swap]


abbrev HasMarkP (h : ℕ → LowerPair) (j : ℕ) (right : Bool) : Prop :=
  HasMark (lowerSide (lowerPhysicalPath h j) right)
private noncomputable def doneAt (h : ℕ → LowerPair) (j : ℕ) (right : Bool) : Bool := by
  classical
  exact if lowerEnds (lowerSide (lowerPhysicalPath h j) right) [3,1,3,1] then true else false
private noncomputable def wideAt (h : ℕ → LowerPair) (j : ℕ) (right : Bool) : Bool := by
  classical
  exact decide (right = (lowerOrientation h j).xor (lowerReflects (h j)))
private def parity (w : List ℕ+) : Bool := decide (w.length % 2 = 1)

private theorem mark_done (h : ℕ → LowerPair) (j : ℕ) (right : Bool)
    (hm : HasMarkP h j right) :
    sf_Marked (lowerSide (lowerPhysicalPath h j) right) (doneAt h j right) := by
  classical
  by_cases hs : lowerEnds (lowerSide (lowerPhysicalPath h j) right) [3,1,3,1]
  · simp [doneAt, sf_Marked, hs]
  · simp [doneAt, sf_Marked, hs]
    exact hm.resolve_right hs

private theorem par_append (w a : List ℕ+) :
    parity (w++a) = (parity w).xor (bitlen a) := by
  unfold parity bitlen
  rcases Nat.mod_two_eq_zero_or_one w.length with hw | hw <;>
    rcases Nat.mod_two_eq_zero_or_one a.length with ha | ha <;>
    simp [List.length_append, Nat.add_mod, hw, ha] <;> omega

private theorem phys_norm_side (h : ℕ → LowerPair) (j : ℕ) (right : Bool) :
    lowerSide (lowerPhysicalPath h j) right =
      if wideAt h j right then (lowerNormalize (h j)).1 else (lowerNormalize (h j)).2 := by
  classical
  cases ho : lowerOrientation h j <;> cases hr : lowerReflects (h j) <;>
    cases right <;> simp [wideAt, lowerPhysicalPath, normalize_reflect, ho, hr,
      lowerSide, Prod.swap]

private theorem wide_next (h : ℕ → LowerPair) (j : ℕ) (right : Bool)
    (l : LowerLabel) (hc : h (j+1)=lowerChild (h j) l) :
    wideAt h (j+1) right = (wideAt h j right).xor (lowerReflects (h (j+1))) := by
  classical
  cases ho : lowerOrientation h j <;> cases hp : lowerReflects (h j) <;>
    cases hn : lowerReflects (h (j+1)) <;> cases right <;>
    simp [wideAt, lowerOrientation, ho, hp, hn]

private theorem marked_increment (h : ℕ → LowerPair) (j : ℕ) (right : Bool)
    (l : LowerLabel) (hc : h (j+1)=lowerChild (h j) l) :
    lowerSide (lowerPhysicalPath h (j+1)) right =
      lowerSide (lowerPhysicalPath h j) right ++
        (if wideAt h j right then l.1.reverse else l.2) := by
  classical
  cases ho : lowerOrientation h j <;> cases hp : lowerReflects (h j) <;>
    cases right <;> simp [wideAt, physical_step h j l hc, ho, hp, lowerSide]

abbrev RunCert (p : LowerPair) : Prop :=
  ∃ u v : List ℕ+, lowerNormalize p = (u++[1],v) ∧
    lowerWidth (u++[1,1]) < lowerWidth v

private theorem rl_of_six {l : LowerLabel} (hs : RelSix l) :
    ∃ r : RL, r.a=l.1.reverse ∧ r.b=l.2 := by
  rcases hs with h|h|h|h|h|h
  · exact ⟨.a1, by simpa [RL.a] using congrArg Prod.fst h.symm,
      by simpa [RL.b] using congrArg Prod.snd h.symm⟩
  · exact ⟨.a2, by simpa [RL.a] using congrArg Prod.fst h.symm,
      by simpa [RL.b] using congrArg Prod.snd h.symm⟩
  · exact ⟨.a3, by simpa [RL.a] using congrArg Prod.fst h.symm,
      by simpa [RL.b] using congrArg Prod.snd h.symm⟩
  · exact ⟨.b1, by simpa [RL.a] using congrArg Prod.fst h.symm,
      by simpa [RL.b] using congrArg Prod.snd h.symm⟩
  · exact ⟨.a2b1, by simpa [RL.a] using congrArg Prod.fst h.symm,
      by simpa [RL.b] using congrArg Prod.snd h.symm⟩
  · exact ⟨.a3b1, by simpa [RL.a] using congrArg Prod.fst h.symm,
      by simpa [RL.b] using congrArg Prod.snd h.symm⟩

private theorem reflect_a23
    (hf : ∀ p, lowerGood p → lowerParameterBox p →
      let q := lowerNormalize p;
      lowerWidth (q.1++[2]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[3]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[1,1]) < lowerWidth q.2 ∧
      lowerWidth (q.2++[1]) < lowerWidth q.1)
    (p : LowerPair) (hg : lowerGood p) (hp : lowerParameterBox p)
    (l : RL) (hl : l=.a2 ∨ l=.a3) :
    lowerReflects (lowerChild p (l.a,l.b)) = true := by
  rcases hl with rfl|rfl
  · have hi := (hf p hg hp).1
    simp [lowerReflects, lowerChild, RL.a, RL.b, hi]
  · have hi := (hf p hg hp).2.1
    simp [lowerReflects, lowerChild, RL.a, RL.b, hi]

private theorem reflect_b1
    (hf : ∀ p, lowerGood p → lowerParameterBox p →
      let q := lowerNormalize p;
      lowerWidth (q.1++[2]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[3]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[1,1]) < lowerWidth q.2 ∧
      lowerWidth (q.2++[1]) < lowerWidth q.1)
    (p : LowerPair) (hg : lowerGood p) (hp : lowerParameterBox p) :
    lowerReflects (lowerChild p (RL.b1.a,RL.b1.b)) = false := by
  have hi := (hf p hg hp).2.2.2
  simp [lowerReflects, lowerChild, RL.a, RL.b, hi, not_lt.mpr hi.le]

private theorem reflect_run (p : LowerPair) (hr : RunCert p) :
    lowerReflects (lowerChild p (RL.a1.a,RL.a1.b)) = true := by
  obtain ⟨u,v,hq,hi⟩ := hr
  simp [lowerReflects, lowerChild, RL.a, RL.b, hq, hi]


abbrev sh_GoodComp (w : List ℕ+) : Prop :=
  ¬ lowerEnds w [3,1] ∧ ¬ lowerEnds w [1,3,1] ∧ ¬ lowerEnds w [3,1,3,1]
abbrev sh_HistDec (l : LowerLabel) : Prop :=
  sh_GoodComp l.1.reverse ∧ sh_GoodComp l.2

private theorem sh_no_suffix_of_false {a b : List ℕ+}
    (h : a.isSuffixOf b = false) : ¬ a.IsSuffix b := by
  intro hs
  have hb := List.isSuffixOf_iff_suffix.mpr hs
  rw [h] at hb
  contradiction
private theorem sh_lstar_of_l (p : LowerPair) (h : ¬ lowerL p) : ¬ lowerLStar p := by
  intro hs
  exact h ((show ([3,1] : List ℕ+).IsSuffix [3,1,3,1] by decide).trans hs)
private theorem sh_rstar_of_r (p : LowerPair) (h : ¬ lowerR p) : ¬ lowerRStar p := by
  intro hs
  exact h ((show ([3,1] : List ℕ+).IsSuffix [3,1,3,1] by decide).trans hs)
private theorem sh_earlyShape (p : LowerPair) (hNL : ¬ lowerL p) (hNRS : ¬ lowerRStar p) :
    ∀ l ∈ lowerEarlyList p, sh_HistDec l := by
  intro l hm
  unfold lowerEarlyList at hm
  split_ifs at hm <;> fin_cases hm <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)

private theorem sh_lateShape (p : LowerPair) (hNLS : ¬ lowerLStar p) :
    ∀ l ∈ lowerLateCandidates, sh_HistDec l := by
  intro l hm
  unfold lowerLateCandidates at hm
  fin_cases hm <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)

private theorem sh_lateMem (p : LowerPair) (l : LowerLabel) (hm : l ∈ lowerLateList p) :
    l ∈ lowerLateCandidates := by
  unfold lowerLateList at hm
  split_ifs at hm with hex
  · exact ((Classical.choose_spec hex).1 l hm).1
  · exact absurd hm (by simp)

private theorem sh_mixShape (p : LowerPair) (l : LowerLabel) (hm : l ∈ lowerMixedList p) :
    sh_HistDec l := by
  unfold lowerMixedList at hm
  split_ifs at hm <;> fin_cases hm <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)

private theorem sh_earlyWrap (p : LowerPair) (l : LowerLabel) (hNL : ¬ lowerL p) (hNRS : ¬ lowerRStar p)
    (hm : l ∈ lowerEarlyList p) : sh_HistDec l := sh_earlyShape p hNL hNRS l hm

private theorem sh_lateWrap (p : LowerPair) (l : LowerLabel) (hNLS : ¬ lowerLStar p)
    (hm : l ∈ lowerLateList p) : sh_HistDec l := sh_lateShape p hNLS l (sh_lateMem p l hm)

private theorem sh_eqShape (p : LowerPair) (l : LowerLabel) (hm : l ∈ lowerEqualList p) :
    sh_HistDec l := by
  unfold lowerEqualList at hm
  split_ifs at hm
  all_goals (try (simp only [*, List.append_nil, List.nil_append] at hm))
  · fin_cases hm <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
  · fin_cases hm <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
  · fin_cases hm <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
  · fin_cases hm <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
  · fin_cases hm <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
  · rw [List.mem_append, List.mem_append] at hm
    rcases hm with (h | h) | h
    · fin_cases h <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
    · exact sh_earlyWrap p l (by assumption) (by assumption) h
    · fin_cases h <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
  · fin_cases hm <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
  · rw [List.mem_append] at hm
    rcases hm with h | h
    · fin_cases h <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
    · exact sh_lateWrap p l (by assumption) h
  · rw [List.mem_append, List.mem_append] at hm
    rcases hm with (h | h) | h
    · fin_cases h <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
    · exact sh_lateWrap p l (by assumption) h
    · fin_cases h <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
  · fin_cases hm <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
  · fin_cases hm <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
  · fin_cases hm <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
  · fin_cases hm <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
  · fin_cases hm <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
  · fin_cases hm <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
  · fin_cases hm <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
  · rw [List.mem_append, List.mem_append] at hm
    rcases hm with (h | h) | h
    · fin_cases h <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
    · exact sh_earlyWrap p l (by assumption) (by assumption) h
    · fin_cases h <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
  · fin_cases hm <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
  · rw [List.mem_append] at hm
    rcases hm with h | h
    · fin_cases h <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
    · exact sh_lateWrap p l (by assumption) h
  · rw [List.mem_append, List.mem_append] at hm
    rcases hm with (h | h) | h
    · fin_cases h <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
    · exact sh_lateWrap p l (by assumption) h
    · fin_cases h <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
  · fin_cases hm <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)
  · fin_cases hm <;> (simp only [sh_HistDec, sh_GoodComp, lowerEnds, Prod.fst, Prod.snd, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]; repeat' first | constructor | (apply sh_no_suffix_of_false; decide) | decide)


private theorem sh_rep_good (k : ℕ) : sh_GoodComp (List.replicate k (3 : ℕ+)) := by
  constructor
  · intro hs
    have hmem : (1 : ℕ+) ∈ List.replicate k (3 : ℕ+) := hs.subset (by decide)
    simpa using List.eq_of_mem_replicate hmem
  constructor
  · intro hs
    have hmem : (1 : ℕ+) ∈ List.replicate k (3 : ℕ+) := hs.subset (by decide)
    simpa using List.eq_of_mem_replicate hmem
  · intro hs
    have hmem : (1 : ℕ+) ∈ List.replicate k (3 : ℕ+) := hs.subset (by decide)
    simpa using List.eq_of_mem_replicate hmem

private theorem sh_offHist (p : LowerPair) (l : LowerLabel) (ho : lowerOffered p l) : sh_HistDec l := by
  classical
  unfold lowerOffered at ho
  rcases ho with hm | ⟨hr, k, hk, rfl⟩
  · by_cases hmix : lowerMixed p
    · rw [if_pos hmix] at hm; exact sh_mixShape p _ hm
    · rw [if_neg hmix] at hm; exact sh_eqShape p _ hm
  · exact ⟨by simpa using sh_rep_good k, sh_rep_good k⟩


private theorem component_data (p : LowerPair) (l : LowerLabel) (ho : lowerOffered p l) :
    let a := l.1.reverse; let b := l.2
    (¬ lowerEnds a [3,1] ∧ ¬ lowerEnds a [1,3,1] ∧ ¬ lowerEnds a [3,1,3] ∧
      ¬ lowerEnds a [3,1,3,1] ∧ a ≠ [1,3]) ∧
    (¬ lowerEnds b [3,1] ∧ ¬ lowerEnds b [1,3,1] ∧ ¬ lowerEnds b [3,1,3] ∧
      ¬ lowerEnds b [3,1,3,1] ∧ b ≠ [1,3]) := by
  have hs := sh_offHist p l ho
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hna,hnb,hne1,hne2⟩ := (offShape p l ho).1
  dsimp
  refine ⟨⟨hs.1.1, hs.1.2.1, ?_, hs.1.2.2, ?_⟩,
    ⟨hs.2.1, hs.2.2.1, hnb, hs.2.2.2, hne2⟩⟩
  · intro hx
    apply hna
    have := List.reverse_prefix.mpr hx
    simpa using this
  · intro he
    apply hne1
    have := congrArg List.reverse he
    simpa using this

private theorem physical_noP (p : LowerPair) (right : Bool) (ha : lowerAdmissible p) :
    noP (lowerSide p right) := by
  have hs := noPparts p.1.reverse p.2 ha.2
  cases right
  · simpa [lowerSide] using noP_rev _ hs.1
  · simpa [lowerSide] using hs.2

noncomputable abbrev Inc (h : ℕ → LowerPair) (j : ℕ) (right : Bool) (l : LowerLabel) :=
  if wideAt h j right then l.1.reverse else l.2

private theorem step_mark_info (h : ℕ → LowerPair) (j : ℕ) (right : Bool)
    (l : LowerLabel) (ho : lowerOffered (h j) l)
    (hc : h (j+1)=lowerChild (h j) l)
    (dp dc : Bool)
    (hp : sf_Marked (lowerSide (lowerPhysicalPath h j) right) dp)
    (hn : sf_Marked (lowerSide (lowerPhysicalPath h (j+1)) right) dc)
    (had : lowerAdmissible (h (j+1))) :
    (Inc h j right l = [] ∧ dp=dc) ∨
      (dp=false ∧ dc=true ∧ Inc h j right l=[1]) := by
  have hd := component_data (h j) l ho
  have hi := marked_increment h j right l hc
  rw [hi] at hn
  have hnp : noP (lowerSide (lowerPhysicalPath h (j+1)) right) := by
    cases hor : lowerOrientation h (j+1) <;> cases right
    · simpa [lowerPhysicalPath, hor, lowerSide] using physical_noP (h (j+1)) false had
    · simpa [lowerPhysicalPath, hor, lowerSide] using physical_noP (h (j+1)) true had
    · simpa [lowerPhysicalPath, hor, lowerSide, Prod.swap] using physical_noP (h (j+1)) true had
    · simpa [lowerPhysicalPath, hor, lowerSide, Prod.swap] using physical_noP (h (j+1)) false had
  rw [hi] at hnp
  cases hw : wideAt h j right
  · simp only [Inc, hw, Bool.false_eq_true, ↓reduceIte]
    simp only [hw, Bool.false_eq_true, ↓reduceIte] at hn hnp
    exact sf_append_marked _ _ dp dc hp hn hd.2.1 hd.2.2.1 hd.2.2.2.1
      hd.2.2.2.2.1 hd.2.2.2.2.2 hnp
  · simp only [Inc, hw, ↓reduceIte]
    simp only [hw, ↓reduceIte] at hn hnp
    exact sf_append_marked _ _ dp dc hp hn hd.1.1 hd.1.2.1 hd.1.2.2.1
      hd.1.2.2.2.1 hd.1.2.2.2.2 hnp

private theorem step_six (h : ℕ → LowerPair) (j : ℕ) (right : Bool)
    (l : LowerLabel) (ho : lowerOffered (h j) l) (dp dc : Bool)
    (hp : sf_Marked (lowerSide (lowerPhysicalPath h j) right) dp)
    (hinc : (Inc h j right l=[] ∧ dp=dc) ∨ (dp=false ∧ dc=true ∧ Inc h j right l=[1])) :
    RelSix l ∧ (l.1=[] → lowerMixed (h j)) := by
  have hm : HasMarkP h j right := by
    cases dp
    · exact Or.inl hp
    · exact Or.inr hp
  have hn := offSix (h j) l ho
  unfold HasMarkP at hm
  rw [phys_norm_side h j right] at hm
  cases hw : wideAt h j right
  · rw [hw] at hm
    have hs : l.2=[] ∨ l.2=[1] := by
      simp only [Inc, hw, Bool.false_eq_true, ↓reduceIte] at hinc
      rcases hinc with ⟨hinc,_⟩ | ⟨_,_,hinc⟩ <;> simp [hinc]
    exact hn.2 hm hs
  · rw [hw] at hm
    have hs : l.1.reverse=[] ∨ l.1.reverse=[1] := by
      simp only [Inc, hw, ↓reduceIte] at hinc
      rcases hinc with ⟨hinc,_⟩ | ⟨_,_,hinc⟩ <;> simp [hinc]
    exact hn.1 hm hs


end GenericLegal16

-- Source: agents.genericdesc16.Match
open Freiman
set_option maxHeartbeats 0
set_option linter.all false
namespace GenericLegal16
attribute [local instance] Classical.propDecidable

private noncomputable def actual (h : ℕ → LowerPair) (j : ℕ) (flip : Bool) : LowerPair :=
  lowerHistoryOrient (lowerPhysicalPath h j) flip

private def Match (h : ℕ → LowerPair) (j : ℕ) (flip basebit : Bool) (s : LowerHistoryState) : Prop :=
  s.wider = GenericDesc16.wideAt h j flip ∧
  lowerHistorySuffixContext (actual h j flip).1 s.context.words.1 ∧
  lowerHistorySuffixContext (actual h j flip).2 s.context.words.2 ∧
  s.context.parity.1 = (parity (actual h j flip).1).xor basebit ∧
  s.context.parity.2 = (parity (actual h j flip).2).xor basebit ∧
  sf_Marked (actual h j flip).2 s.markedDone ∧
  (s.previous = some (false,([1],[]),false) → RunCert (h j))

private theorem wideAt_complement (h : ℕ → LowerPair) (j : ℕ) (flip : Bool) :
    wideAt h j (!flip) = GenericDesc16.wideAt h j flip := by
  cases ho : lowerOrientation h j <;> cases hr : lowerReflects (h j) <;> cases flip <;>
    simp [wideAt, GenericDesc16.wideAt, ho, hr]

private theorem suffixContext_snoc (u v : List ℕ+) (a : ℕ+)
    (h : lowerHistorySuffixContext u v) :
    lowerHistorySuffixContext (u++[a]) (v++[a]) := by
  rcases h with ⟨⟨pre,hpre⟩,h3,h31⟩
  refine ⟨⟨pre,by simpa [List.append_assoc] using congrArg (fun z => z ++ [a]) hpre⟩,?_,?_⟩
  · simp [lowerEnds, ← List.reverse_prefix]
  · have h3r : [3] <+: u.reverse ↔ [3] <+: v.reverse := by
      simpa [lowerEnds, ← List.reverse_prefix] using h3
    simp [lowerEnds, ← List.reverse_prefix, h3r]

private theorem suffixContext_append (u v w : List ℕ+)
    (h : lowerHistorySuffixContext u v) :
    lowerHistorySuffixContext (u++w) (v++w) := by
  induction w using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton w a ih =>
      simpa [List.append_assoc] using suffixContext_snoc (u++w) (v++w) a ih

private theorem forbidden_false (w : List ℕ+) (hn : noP w) : lowerHistoryForbidden w = false := by
  simp only [lowerHistoryForbidden, List.any_eq_false]
  intro n hnmem
  simp only [decide_eq_true_eq]
  intro he
  apply hn
  rw [← he]
  exact (List.take_prefix 5 (w.drop n)).isInfix.trans (List.drop_suffix n w).isInfix

private theorem actual_noP (h : ℕ → LowerPair) (j : ℕ) (flip : Bool)
    (had : lowerAdmissible (h j)) : noP (actual h j flip).1 ∧ noP (actual h j flip).2 := by
  have hl := physical_noP (h j) false had
  have hr := physical_noP (h j) true had
  cases ho : lowerOrientation h j <;> cases flip <;>
    simp only [actual, lowerPhysicalPath, lowerHistoryOrient, lowerSide, ho, Bool.false_eq_true, ↓reduceIte, Prod.swap] <;>
    first | exact ⟨hl,hr⟩ | exact ⟨hr,hl⟩

private theorem match_mixed (h : ℕ → LowerPair) (j : ℕ) (flip basebit : Bool)
    (s : LowerHistoryState) (hm : Match h j flip basebit s) :
    lowerMixed (h j) ↔ s.context.parity.1 ≠ s.context.parity.2 := by
  obtain ⟨_,_,_,hp,hq,_,_⟩ := hm
  rw [hp,hq]
  cases ho : lowerOrientation h j <;> cases flip <;> cases basebit <;>
    rcases Nat.mod_two_eq_zero_or_one (h j).1.length with h1|h1 <;>
    rcases Nat.mod_two_eq_zero_or_one (h j).2.length with h2|h2 <;>
    simp [actual, lowerPhysicalPath, lowerHistoryOrient, ho, lowerMixed, parity, h1, h2]

end GenericLegal16

-- Source: agents.genericdesc16.StepLegal
open Freiman
set_option maxHeartbeats 0
set_option linter.all false
namespace GenericLegal16
attribute [local instance] Classical.propDecidable

private theorem step_legal_of_match
    (hf : ∀ p, lowerGood p → lowerParameterBox p →
      let q := lowerNormalize p;
      lowerWidth (q.1++[2]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[3]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[1,1]) < lowerWidth q.2 ∧
      lowerWidth (q.2++[1]) < lowerWidth q.1)
    (h : ℕ → LowerPair) (j : ℕ) (flip basebit : Bool) (s : LowerHistoryState)
    (l : LowerLabel) (ho : lowerOffered (h j) l)
    (hc : h (j+1) = lowerChild (h j) l)
    (hg : lowerGood (h j)) (hbox : lowerParameterBox (h j))
    (had : lowerAdmissible (h (j+1)))
    (hm : Match h j flip basebit s)
    (hn : Match h (j+1) flip basebit (lowerHistoryAdvance s l (lowerReflects (h (j+1))))) :
    lowerHistoryStepLegal s l (lowerReflects (h (j+1))) := by
  have hmixed := match_mixed h j flip basebit s hm
  obtain ⟨hw,hctx1,hctx2,_,_,hmark,hrun⟩ := hm
  obtain ⟨_,hnctx1,hnctx2,_,_,hnmark,_⟩ := hn
  have hp : sf_Marked (lowerSide (lowerPhysicalPath h j) (!flip)) s.markedDone := by
    simpa only [actual,GenericDesc16.orient_side] using hmark
  have hnp : sf_Marked (lowerSide (lowerPhysicalPath h (j+1)) (!flip))
      (lowerHistoryAdvance s l (lowerReflects (h (j+1)))).markedDone := by
    simpa only [actual,GenericDesc16.orient_side] using hnmark
  have hinc := step_mark_info h j (!flip) l ho hc _ _ hp hnp had
  have hsix := step_six h j (!flip) l ho _ _ hp hinc
  have hi : Inc h j (!flip) l = (lowerHistoryRawStep ([],[]) s.wider l).2 := by
    simp only [Inc,wideAt_complement,←hw,lowerHistoryRawStep]
    cases s.wider <;> simp
  rw [hi] at hinc
  have hnorm := GenericDesc16.normalize_physical h j flip
  change lowerNormalize (h j) = lowerHistoryOrient (actual h j flip) _ at hnorm
  rw [← hw] at hnorm
  have hnpair := actual_noP h (j+1) flip had
  obtain ⟨rl,ha,hb⟩ := rl_of_six hsix.1
  have hra : rl.a.reverse = rl.a := by cases rl <;> decide
  have hlab : l = (rl.a,rl.b) := Prod.ext
    (by rw [← List.reverse_reverse l.1, ← ha, hra]) hb.symm
  have hmem : l ∈ lowerHistoryLabels := by
    rw [hlab]
    cases rl <;> decide
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact hmem
  · exact fun he => hmixed.mp (hsix.2 he)
  · intro hl he
    apply (offShape (h j) l ho).2.2.2.1 hl
    unfold lowerL
    rw [hnorm]
    cases hw' : s.wider
    · exact hctx1.2.2.mpr (by simpa [lowerHistoryPick,hw'] using he)
    · exact hctx2.2.2.mpr (by simpa [lowerHistoryPick,hw'] using he)
  · rcases hinc with ⟨he,_⟩ | ⟨_,_,he⟩ <;> simp [he]
  · intro hd
    rcases hinc with ⟨he,_⟩ | ⟨he,_,_⟩
    · exact he
    · simp [hd] at he
  · apply forbidden_false
    exact fun hx => hnpair.1 (hx.trans hnctx1.1.isInfix)
  · apply forbidden_false
    exact fun hx => hnpair.2 (hx.trans hnctx2.1.isInfix)
  · intro he
    have hl : l = ([],[1]) := by
      have hx := hmem
      simp only [lowerHistoryLabels,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> simp_all
    rw [hc,hl]
    exact reflect_b1 hf (h j) hg hbox
  · intro he hl
    rcases hl with hl|hl
    · have hlab : l = ([2],[]) := Prod.ext hl he
      rw [hc,hlab]
      exact reflect_a23 hf (h j) hg hbox .a2 (Or.inl rfl)
    · have hlab : l = ([3],[]) := Prod.ext hl he
      rw [hc,hlab]
      exact reflect_a23 hf (h j) hg hbox .a3 (Or.inr rfl)
  · intro hwide _ hl hpv
    have hr := reflect_run (h j) (hrun hpv)
    have hr' : lowerReflects (h (j+1)) = true := by
      simpa only [hc,hl,RL.a,RL.b] using hr
    simp [lowerHistoryAdvance,hwide,hr']

end GenericLegal16

-- Source: agents.genericdesc16.Advance
open Freiman
set_option maxHeartbeats 0
set_option linter.all false
namespace GenericLegal16
attribute [local instance] Classical.propDecidable

private theorem match_next
    (hf : ∀ p, lowerGood p → lowerParameterBox p →
      let q := lowerNormalize p;
      lowerWidth (q.1++[2]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[3]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[1,1]) < lowerWidth q.2 ∧
      lowerWidth (q.2++[1]) < lowerWidth q.1)
    (h : ℕ → LowerPair) (j : ℕ) (flip basebit : Bool) (s : LowerHistoryState)
    (l : LowerLabel) (ho : lowerOffered (h j) l)
    (hc : h (j+1) = lowerChild (h j) l)
    (hg : lowerGood (h j)) (hbox : lowerParameterBox (h j))
    (had : lowerAdmissible (h (j+1)))
    (hm : Match h j flip basebit s)
    (hmarked : HasMark (actual h (j+1) flip).2) :
    Match h (j+1) flip basebit (lowerHistoryAdvance s l (lowerReflects (h (j+1)))) := by
  obtain ⟨hw,hctx1,hctx2,hp,hq,hmark,_⟩ := hm
  have hnext : actual h (j+1) flip = lowerHistoryRawStep (actual h j flip) s.wider l := by
    simpa only [actual,hw] using GenericDesc16.physical_step h j l flip hc
  have hmark' : HasMarkP h (j+1) (!flip) := by
    simpa only [actual,GenericDesc16.orient_side] using hmarked
  let dc := doneAt h (j+1) (!flip)
  have hdc := mark_done h (j+1) (!flip) hmark'
  have hdp : sf_Marked (lowerSide (lowerPhysicalPath h j) (!flip)) s.markedDone := by
    simpa only [actual,GenericDesc16.orient_side] using hmark
  have hinc := step_mark_info h j (!flip) l ho hc s.markedDone dc hdp hdc had
  have hi : Inc h j (!flip) l = (lowerHistoryRawStep ([],[]) s.wider l).2 := by
    simp only [Inc,wideAt_complement,←hw,lowerHistoryRawStep]
    cases s.wider <;> simp
  rw [hi] at hinc
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · change s.wider.xor (lowerReflects (h (j+1))) = _
    rw [hw,GenericDesc16.wide_next]
    cases GenericDesc16.wideAt h j flip <;> cases lowerReflects (h (j+1)) <;> rfl
  · rw [hnext]
    cases hs : s.wider <;>
      simpa [lowerHistoryAdvance,lowerHistoryRawStep,hs] using
        suffixContext_append _ _ (if hs' : s.wider then l.2 else l.1.reverse) hctx1
  · rw [hnext]
    cases hs : s.wider <;>
      simpa [lowerHistoryAdvance,lowerHistoryRawStep,hs] using
        suffixContext_append _ _ (if hs' : s.wider then l.1.reverse else l.2) hctx2
  · rw [hnext]
    cases hs : s.wider <;>
      simp [lowerHistoryAdvance,lowerHistoryRawStep,hs,par_append,hp,bitlen,
        Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]
  · rw [hnext]
    cases hs : s.wider <;>
      simp [lowerHistoryAdvance,lowerHistoryRawStep,hs,par_append,hq,bitlen,
        Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]
  · have he : (lowerHistoryAdvance s l (lowerReflects (h (j+1)))).markedDone = dc := by
      rcases hinc with ⟨he,hd⟩ | ⟨hd,hc,he⟩
      · simp [lowerHistoryAdvance,he,hd]
      · simp [lowerHistoryAdvance,he,hd,hc]
    rw [he]
    simpa only [actual,GenericDesc16.orient_side] using hdc
  · intro he
    change some (s.wider,l,lowerReflects (h (j+1))) = some (false,([1],[]),false) at he
    simp only [Option.some.injEq,Prod.mk.injEq] at he
    obtain ⟨_,hl,hr⟩ := he
    have hr' : lowerReflects (lowerChild (h j) ([1],[])) = false := by simpa [hc,hl] using hr
    unfold RunCert
    rw [hc,hl,normalize_reflect,hr']
    refine ⟨(lowerNormalize (h j)).1,(lowerNormalize (h j)).2,?_,(hf (h j) hg hbox).2.2.1⟩
    simp [lowerChild]

end GenericLegal16

-- Source: agents.genericdesc16.Structural
open Freiman
namespace GenericDesc16

private def catalog (row : ℕ) : LowerHistoryCatalog :=
  if row=1 then .left else if row=2 then .right else if row=3 then .mixed else .rightMixed

private def stateTrace (ctx : List ℕ+) (wide : Bool) (steps : List (LowerLabel × Bool)) : LowerHistoryState :=
  lowerHistoryFinalState
    ⟨.left,0,ctx,([2],[3]),wide,steps,([],[]),(false,false),false,0,⟨0,1,0,1⟩,0⟩

private def descriptor (ctx : List ℕ+) (wide : Bool) (steps : List (LowerLabel × Bool))
    (row : ℕ) : LowerHistoryPath :=
  let s := stateTrace ctx wide steps
  ⟨catalog row,0,ctx,([2],[3]),wide,steps,s.context.words,s.context.parity,s.wider,row,⟨0,1,0,1⟩,0⟩

private theorem catalog_not_initial (row : ℕ) : catalog row ≠ .initial := by
  unfold catalog
  split_ifs <;> decide

private theorem descriptor_initial (ctx : List ℕ+) (wide : Bool)
    (steps : List (LowerLabel × Bool)) (row : ℕ) :
    lowerHistoryInitialState (descriptor ctx wide steps row) =
      lowerHistoryInitialState
        ⟨.left,0,ctx,([2],[3]),wide,steps,([],[]),(false,false),false,0,⟨0,1,0,1⟩,0⟩ := by
  simp [descriptor, lowerHistoryInitialState, catalog_not_initial]

private theorem descriptor_final (ctx : List ℕ+) (wide : Bool)
    (steps : List (LowerLabel × Bool)) (row : ℕ) :
    lowerHistoryFinalState (descriptor ctx wide steps row) = stateTrace ctx wide steps := by
  unfold lowerHistoryFinalState
  rw [descriptor_initial]
  rfl

private theorem descriptor_structural (ctx : List ℕ+) (wide : Bool)
    (steps : List (LowerLabel × Bool)) (row : ℕ)
    (hlen : steps.length ≤ 7) (hctx : ctx ∈ lowerHistoryContextWords)
    (hlegal : lowerHistoryLegalSteps
      (lowerHistoryInitialState (descriptor ctx wide steps row)) steps)
    (hmarked : (stateTrace ctx wide steps).markedDone = true)
    (hparity : (stateTrace ctx wide steps).context.parity.2 = false)
    (hrow : row = if (stateTrace ctx wide steps).context.parity.1 then
      if (stateTrace ctx wide steps).wider then 3 else 4
      else if (stateTrace ctx wide steps).wider then 1 else 2) :
    lowerHistoryStructural (descriptor ctx wide steps row) := by
  refine ⟨hlen,?_,hlegal,?_,?_⟩
  · simp only [descriptor, catalog_not_initial, ↓reduceIte]
    exact ⟨hctx,trivial⟩
  · rw [descriptor_final]
    exact ⟨hmarked,rfl,rfl,rfl⟩
  · simp only [descriptor, catalog_not_initial, ↓reduceIte]
    have he : (stateTrace ctx wide steps).context.parity =
        ((stateTrace ctx wide steps).context.parity.1,false) := Prod.ext rfl hparity
    rw [he]
    cases hp : (stateTrace ctx wide steps).context.parity.1 <;>
      cases hw : (stateTrace ctx wide steps).wider <;>
      simp only [hp, hw, Bool.false_eq_true, ↓reduceIte] at hrow <;>
      subst row <;> simp [catalog, hp, hw]

private theorem descriptor_reached (t : ℝ) (h : ℕ → LowerPair) (n m : ℕ)
    (ctx : List ℕ+) (wide : Bool) (steps : List (LowerLabel × Bool)) (row : ℕ)
    (hm : 0 < m) (hlen : m + steps.length = n)
    (hreal : lowerHistoryRealizes h m (lowerNormalize (h (m-1)))
      (lowerOrientation h m) (descriptor ctx wide steps row)) :
    lowerHistoryReached t h n (lowerNormalize (h (m-1))) (descriptor ctx wide steps row) := by
  refine ⟨m, lowerOrientation h m, hlen, hreal, ?_⟩
  simp only [descriptor, catalog_not_initial, ↓reduceIte]
  exact ⟨hm,trivial,birth_orient_before h m hm,trivial⟩

end GenericDesc16

-- Source: agents.genericdesc16.Fold
open Freiman
set_option maxHeartbeats 0
set_option linter.all false
namespace GenericLegal16
attribute [local instance] Classical.propDecidable

private def foldState (s : LowerHistoryState) (steps : List (LowerLabel × Bool)) : LowerHistoryState :=
  steps.foldl (fun s step => lowerHistoryAdvance s step.1 step.2) s

private theorem legal_append (s : LowerHistoryState) (as bs : List (LowerLabel × Bool))
    (ha : lowerHistoryLegalSteps s as) (hb : lowerHistoryLegalSteps (foldState s as) bs) :
    lowerHistoryLegalSteps s (as++bs) := by
  induction as generalizing s with
  | nil => exact hb
  | cons a as ih => exact ⟨ha.1,ih _ ha.2 hb⟩

private theorem trace_matched
    (hf : ∀ p, lowerGood p → lowerParameterBox p →
      let q := lowerNormalize p;
      lowerWidth (q.1++[2]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[3]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[1,1]) < lowerWidth q.2 ∧
      lowerWidth (q.2++[1]) < lowerWidth q.1)
    (t : ℝ) (h : ℕ → LowerPair) (N start n : ℕ) (flip basebit : Bool)
    (hh : lowerHistory t h N) (hbound : start+n ≤ N)
    (labels : ℕ → LowerLabel)
    (hl : ∀ j < N, lowerOffered (h j) (labels j) ∧
      lowerPriority t (h j) (labels j) ∧ h (j+1)=lowerChild (h j) (labels j))
    (s : LowerHistoryState) (hm : Match h start flip basebit s)
    (hmark : ∀ j ≤ n, HasMark (actual h (start+j) flip).2) :
    lowerHistoryLegalSteps s (GenericDesc16.trace h labels start n) ∧
    Match h (start+n) flip basebit (foldState s (GenericDesc16.trace h labels start n)) := by
  induction n with
  | zero => exact ⟨trivial,by simpa [GenericDesc16.trace,foldState] using hm⟩
  | succ n ih =>
    obtain ⟨hlegal,hmatched⟩ := ih (by omega) (fun j hj => hmark j (by omega))
    have hj : start+n < N := by omega
    obtain ⟨ho,_,hc⟩ := hl (start+n) hj
    have hst := hh.2.1 (start+n) (by omega)
    have hstn := hh.2.1 (start+n+1) (by omega)
    have hmn := match_next hf h (start+n) flip basebit _ _ ho hc hst.2.1 hst.2.2.2
      hstn.1 hmatched (by simpa [Nat.add_assoc] using hmark (n+1) (by omega))
    have hstep := step_legal_of_match hf h (start+n) flip basebit _ _ ho hc
      hst.2.1 hst.2.2.2 hstn.1 hmatched hmn
    constructor
    · rw [GenericDesc16.trace]
      exact legal_append _ _ _ hlegal ⟨hstep,trivial⟩
    · simpa [GenericDesc16.trace,foldState,List.foldl_append,Nat.add_assoc] using hmn

end GenericLegal16

-- Source: agents.genericdesc16.Initial
open Freiman
set_option maxHeartbeats 0
set_option linter.all false
namespace GenericLegal16
attribute [local instance] Classical.propDecidable

private def startState (ctx : List ℕ+) (wide : Bool) : LowerHistoryState :=
  ⟨⟨(ctx++[2],[3,1,3]),(true,true)⟩,wide,false,none⟩

private theorem descriptor_start (ctx : List ℕ+) (wide : Bool) (steps : List (LowerLabel × Bool)) (row : ℕ) :
    lowerHistoryInitialState (GenericDesc16.descriptor ctx wide steps row) = startState ctx wide := by
  rw [GenericDesc16.descriptor_initial]
  rfl

private theorem context_31 (w : List ℕ+) (hw : lowerEnds w [3,1]) :
    lowerHistorySuffixContext w [3,1] := by
  rcases hw with ⟨pre,rfl⟩
  simp [lowerHistorySuffixContext,lowerEnds,← List.reverse_prefix]

private theorem birth_match (h : ℕ → LowerPair) (m : ℕ) (ctx : List ℕ+)
    (hctx : lowerHistorySuffixContext (lowerNormalize (h (m-1))).1 ctx)
    (hb : lowerEnds (lowerNormalize (h (m-1))).2 [3,1])
    (hp : (lowerNormalize (h (m-1))).1.length%2 = (lowerNormalize (h (m-1))).2.length%2)
    (hbirth : h m = lowerChild (h (m-1)) ([2],[3])) :
    Match h m (lowerOrientation h m) (parity (lowerNormalize (h (m-1))).1)
      (startState ctx (GenericDesc16.wideAt h m (lowerOrientation h m))) := by
  let base := lowerNormalize (h (m-1))
  have ha : actual h m (lowerOrientation h m) = (base.1++[2],base.2++[3]) := by
    rw [actual,GenericDesc16.birth_orient_at,hbirth]
    rfl
  have hpb : parity base.1 = parity base.2 := by simp only [parity,base,hp]
  have ht : lowerHistorySuffixContext (base.2++[3]) [3,1,3] :=
    suffixContext_append _ _ [3] (context_31 _ hb)
  refine ⟨rfl,?_,?_,?_,?_,?_,?_⟩
  · rw [ha]
    exact suffixContext_append _ _ [2] hctx
  · rw [ha]
    exact ht
  · rw [ha]
    change true = (parity (base.1++[2])).xor (parity base.1)
    rw [par_append]
    cases parity base.1 <;> rfl
  · rw [ha]
    change true = (parity (base.2++[3])).xor (parity base.1)
    rw [par_append, hpb]
    cases parity base.2 <;> rfl
  · rw [ha]
    exact ht.1
  · simp [startState]

end GenericLegal16

-- Source: agents.genericdesc16.MarkedParity
open Freiman
set_option linter.all false
namespace GenericLegal16

private theorem advance_marked_parity (s : LowerHistoryState) (l : LowerLabel) (r : Bool)
    (hl : lowerHistoryStepLegal s l r)
    (hp : s.context.parity.2 = !s.markedDone) :
    (lowerHistoryAdvance s l r).context.parity.2 = !(lowerHistoryAdvance s l r).markedDone := by
  have he := hl.2.2.2.1
  have hd := hl.2.2.2.2.1
  rcases he with he|he
  · simp [lowerHistoryAdvance,he,hp]
  · have hm : s.markedDone = false := by
      cases hm : s.markedDone
      · rfl
      · have hz := hd hm
        rw [he] at hz
        contradiction
    simp [lowerHistoryAdvance,he,hp,hm]

private theorem legal_marked_parity (s : LowerHistoryState) (steps : List (LowerLabel × Bool))
    (hl : lowerHistoryLegalSteps s steps)
    (hp : s.context.parity.2 = !s.markedDone) :
    (foldState s steps).context.parity.2 = !(foldState s steps).markedDone := by
  induction steps generalizing s with
  | nil => exact hp
  | cons a steps ih => exact ih _ hl.2 (advance_marked_parity s a.1 a.2 hl.1 hp)

end GenericLegal16

-- Source: agents.genericdesc16.Assembly
open Freiman
set_option maxHeartbeats 0
set_option linter.all false
namespace GenericDesc16
attribute [local instance] Classical.propDecidable

abbrev TerminalLaw : Prop := ∀ (h : ℕ → LowerPair) (n row : ℕ) (flip bit : Bool)
    (s : LowerHistoryState), row ∈ [1,2,3,4] → lowerHistoryHazard row (h n) →
    flip = !(lowerMarkedPhysical h n row) → GenericLegal16.Match h n flip bit s →
    s.markedDone = true ∧
      row = if s.context.parity.1 = s.context.parity.2 then
        if s.wider then 1 else 2 else if s.wider then 3 else 4

private theorem generic_descriptor_of_terminal (ht : TerminalLaw)
    (hf : ∀ p, lowerGood p → lowerParameterBox p →
      let q := lowerNormalize p;
      lowerWidth (q.1++[2]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[3]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[1,1]) < lowerWidth q.2 ∧
      lowerWidth (q.2++[1]) < lowerWidth q.1)
    (t : ℝ) (h : ℕ → LowerPair) (n row : ℕ) (hh : lowerHistory t h n)
    (hrow : row ∈ [1,2,3,4]) (haz : lowerHistoryHazard row (h n))
    (hm : lowerGenericMarked h n (lowerMarkedPhysical h n row)) :
    ∃ base p, lowerHistoryStructural p ∧ lowerHistoryReached t h n base p ∧ p.row = row := by
  obtain ⟨m,ctx,hm0,hmn,hlen,hctxmem,hctx,hbsuffix,hnstar,hpar,hbirth,hright,hpres⟩ :=
    generic_span_data t h n _ hh hm
  obtain ⟨labels,hl⟩ := actual_labels t h n hh
  let flip := lowerOrientation h m
  let bit := GenericLegal16.parity (lowerNormalize (h (m-1))).1
  let wide := wideAt h m flip
  let steps := trace h labels m (n-m)
  let s0 := GenericLegal16.startState ctx wide
  let p := descriptor ctx wide steps row
  let base := lowerNormalize (h (m-1))
  have hinit : GenericLegal16.Match h m flip bit s0 :=
    GenericLegal16.birth_match h m ctx hctx hbsuffix hpar hbirth
  have hpres' : ∀ j ≤ n-m, GenericLegal16.HasMark (GenericLegal16.actual h (m+j) flip).2 := by
    intro j hj
    exact hpres (m+j) (by omega) (by omega)
  have hfold := GenericLegal16.trace_matched hf t h n m (n-m) flip bit hh (by omega)
    labels hl s0 hinit hpres'
  have hleg : lowerHistoryLegalSteps (lowerHistoryInitialState p) steps := by
    rw [show lowerHistoryInitialState p = s0 from GenericLegal16.descriptor_start ctx wide steps row]
    exact hfold.1
  have hmfinal : GenericLegal16.Match h n flip bit (stateTrace ctx wide steps) := by
    change GenericLegal16.Match h n flip bit (GenericLegal16.foldState s0 steps)
    simpa [steps,show m+(n-m)=n by omega] using hfold.2
  have hflip : flip = !(lowerMarkedPhysical h n row) := by
    rw [hright]
    simp [flip]
  obtain ⟨hdone,hrowfinal⟩ := ht h n row flip bit _ hrow haz hflip hmfinal
  have hpmarked := GenericLegal16.legal_marked_parity s0 steps hfold.1 (by rfl)
  have hp2 : (stateTrace ctx wide steps).context.parity.2 = false := by
    change (GenericLegal16.foldState s0 steps).context.parity.2 = false
    change (GenericLegal16.foldState s0 steps).markedDone = true at hdone
    simpa only [hdone,Bool.not_true] using hpmarked
  have hrowgeneric : row = if (stateTrace ctx wide steps).context.parity.1 then
      if (stateTrace ctx wide steps).wider then 3 else 4
      else if (stateTrace ctx wide steps).wider then 1 else 2 := by
    rw [hp2] at hrowfinal
    cases hp1 : (stateTrace ctx wide steps).context.parity.1 <;> simpa [hp1] using hrowfinal
  have hstruct : lowerHistoryStructural p := descriptor_structural ctx wide steps row
    (by simpa [steps] using hlen) hctxmem hleg hdone hp2 hrowgeneric
  have hreal : lowerHistoryRealizes h m base flip p := by
    apply realizes_of_trace h labels m (n-m) base p flip rfl hctx
    · simp only [p,descriptor,catalog_not_initial,↓reduceIte]
      exact ⟨hbsuffix,hnstar⟩
    · exact hpar
    · exact birth_entry h m hbirth
    · rfl
    · intro j hj
      exact (hl (m+j) (by omega)).2.2
  refine ⟨base,p,hstruct,?_,rfl⟩
  exact descriptor_reached t h n m ctx wide steps row hm0 (by simp [steps]; omega) hreal

end GenericDesc16

-- Source: agents.initialdesc16.TerminalMatch
open Freiman
set_option maxHeartbeats 0
set_option linter.all false
namespace InitialDesc16
attribute [local instance] Classical.propDecidable
open GenericLegal16

private theorem marked_wide (h : ℕ → LowerPair) (n row : ℕ)
    (hrow : row ∈ [1,2,3,4]) :
    GenericDesc16.wideAt h n (!(lowerMarkedPhysical h n row)) =
      decide (row=1 ∨ row=3) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hrow
  rcases hrow with rfl|rfl|rfl|rfl <;>
    cases ho : lowerOrientation h n <;> cases hr : lowerReflects (h n) <;>
    simp [lowerMarkedPhysical,GenericDesc16.wideAt,ho,hr]

private theorem marked_actual_second (h : ℕ → LowerPair) (n row : ℕ) (flip : Bool)
    (hrow : row ∈ [1,2,3,4]) (haz : lowerHistoryHazard row (h n))
    (hflip : flip = !(lowerMarkedPhysical h n row)) :
    lowerEnds (GenericLegal16.actual h n flip).2 [3,1,3,1] := by
  subst flip
  have hn := GenericDesc16.normalize_physical h n (!(lowerMarkedPhysical h n row))
  have hw := marked_wide h n row hrow
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hrow
  rcases hrow with rfl|rfl|rfl|rfl
  all_goals simp only [lowerHistoryHazard] at haz
  · have he : (lowerNormalize (h n)).1 =
        (GenericLegal16.actual h n (!(lowerMarkedPhysical h n 1))).2 := by
      rw [hn,hw]
      simp [GenericLegal16.actual,lowerHistoryOrient]
    rw [← he]
    exact haz.2.2.2
  · have he : (lowerNormalize (h n)).2 =
        (GenericLegal16.actual h n (!(lowerMarkedPhysical h n 2))).2 := by
      rw [hn,hw]
      simp [GenericLegal16.actual,lowerHistoryOrient]
    rw [← he]
    exact haz.2.2
  · have he : (lowerNormalize (h n)).1 =
        (GenericLegal16.actual h n (!(lowerMarkedPhysical h n 3))).2 := by
      rw [hn,hw]
      simp [GenericLegal16.actual,lowerHistoryOrient]
    rw [← he]
    exact haz.2.2.2
  · have he : (lowerNormalize (h n)).2 =
        (GenericLegal16.actual h n (!(lowerMarkedPhysical h n 4))).2 := by
      rw [hn,hw]
      simp [GenericLegal16.actual,lowerHistoryOrient]
    rw [← he]
    exact haz.2.2.2

private theorem not_both_suffix (w : List ℕ+)
    (h3 : lowerEnds w [3,1,3]) (h1 : lowerEnds w [3,1,3,1]) : False := by
  rcases h3 with ⟨a,ha⟩
  rcases h1 with ⟨b,hb⟩
  have ea := congrArg List.getLast? ha
  have eb := congrArg List.getLast? hb
  simp at ea eb
  rw [← ea] at eb
  contradiction

private theorem terminal_data (h : ℕ → LowerPair) (n row : ℕ) (flip basebit : Bool)
    (s : LowerHistoryState) (hrow : row ∈ [1,2,3,4])
    (haz : lowerHistoryHazard row (h n))
    (hflip : flip = !(lowerMarkedPhysical h n row))
    (hm : GenericLegal16.Match h n flip basebit s) :
    s.markedDone = true ∧
    row = (if s.context.parity.1 = s.context.parity.2 then
      if s.wider then 1 else 2 else if s.wider then 3 else 4) := by
  have hend := marked_actual_second h n row flip hrow haz hflip
  have hdone : s.markedDone=true := by
    have hs := hm.2.2.2.2.2.1
    cases hd : s.markedDone
    · exact (not_both_suffix _ (by simpa [GenericLegal16.sf_Marked,hd] using hs) hend).elim
    · rfl
  refine ⟨hdone,?_⟩
  have hmix := GenericLegal16.match_mixed h n flip basebit s hm
  have hw : s.wider = decide (row=1 ∨ row=3) := by
    rw [hm.1,hflip,marked_wide h n row hrow]
  rw [hw]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hrow
  rcases hrow with rfl|rfl|rfl|rfl <;>
    simp only [lowerHistoryHazard] at haz <;> simp_all

end InitialDesc16

-- Source: agents.genericdesc16.Final
open Freiman

theorem solution (hf : ∀ (p : LowerPair), lowerGood p → lowerParameterBox p → let q := lowerNormalize p;
    lowerWidth (q.1++[2]) < lowerWidth q.2 ∧ lowerWidth (q.1++[3]) < lowerWidth q.2 ∧
    lowerWidth (q.1++[1,1]) < lowerWidth q.2 ∧ lowerWidth (q.2++[1]) < lowerWidth q.1)
    (t : ℝ) (h : ℕ → LowerPair) (n row : ℕ) (hh : lowerHistory t h n)
    (hrow : row ∈ [1,2,3,4]) (haz : lowerHistoryHazard row (h n))
    (hm : lowerGenericMarked h n (lowerMarkedPhysical h n row)) :
    ∃ base p, lowerHistoryStructural p ∧ lowerHistoryReached t h n base p ∧ p.row = row := by
  exact GenericDesc16.generic_descriptor_of_terminal InitialDesc16.terminal_data hf t h n row hh hrow haz hm


#print axioms solution
