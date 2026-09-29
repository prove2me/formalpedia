-- Prove2me | solution 1 for Freiman.lower_history_window_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T16:15:26.165764+00:00
-- url     : https://prove2.me/submissions/4b04bb13-1336-45a2-8f7e-2eb7c8be8671

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic
open Freiman
set_option maxHeartbeats 0




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




private abbrev RelSix (l : LowerLabel) : Prop :=
  (l.1.reverse, l.2) = ([1],[]) ∨ (l.1.reverse,l.2) = ([2],[]) ∨
  (l.1.reverse,l.2) = ([3],[]) ∨ (l.1.reverse,l.2) = ([],[1]) ∨
  (l.1.reverse,l.2) = ([2],[1]) ∨ (l.1.reverse,l.2) = ([3],[1])
private abbrev HasMark (w : List ℕ+) : Prop :=
  lowerEnds w [3,1,3] ∨ lowerEnds w [3,1,3,1]
private abbrev SixDec (p : LowerPair) (l : LowerLabel) : Prop :=
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



private abbrev sf_Marked (w : List ℕ+) (done : Bool) : Prop :=
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



private inductive RL where | a1 | a2 | a3 | b1 | a2b1 | a3b1
  deriving DecidableEq, Repr

private def RL.all : List RL := [.a1,.a2,.a3,.b1,.a2b1,.a3b1]
private def RL.a : RL → List ℕ+
  | .a1 => [1] | .a2 => [2] | .a3 => [3] | .b1 => []
  | .a2b1 => [2] | .a3b1 => [3]
private def RL.b : RL → List ℕ+
  | .a1 | .a2 | .a3 => [] | .b1 | .a2b1 | .a3b1 => [1]

private structure WS where
  wide : Bool
  p0 : Bool
  p1 : Bool
  done : Bool
  run : Bool
  deriving DecidableEq, Repr

private def bitlen (w : List ℕ+) : Bool := decide (w.length % 2 = 1)
private def raw0 (s : WS) (l : RL) := s.p0.xor (bitlen l.a)
private def raw1 (s : WS) (l : RL) := s.p1.xor (bitlen l.b)
private def marked (s : WS) (l : RL) := if s.wide then l.a else l.b
private def permitted (s : WS) (l : RL) (r : Bool) : Bool :=
  -- An addition on normalized side two with side one empty is offered only in
  -- mixed parity.  The marked side stays empty, or receives its unique 1.
  (!(l.a == []) || s.p0 != s.p1) &&
  (marked s l == [] || (!s.done && marked s l == [1])) &&
  -- The four width comparisons force these normalizations.  The third one
  -- applies after a preceding unreflected one-sided 1 on the narrower side.
  (if l = .a2 || l = .a3 then r else true) &&
  (if l = .b1 then !r else true) &&
  (if l = .a1 && !s.wide && s.run then r else true)

private def next (s : WS) (l : RL) (r : Bool) : WS :=
  { wide := s.wide.xor r
    p0 := if r then raw1 s l else raw0 s l
    p1 := if r then raw0 s l else raw1 s l
    done := s.done || marked s l == [1]
    run := l = .a1 && !s.wide && !r }

private def succ (s : WS) : List WS :=
  RL.all.flatMap fun l => [false,true].filterMap fun r =>
    if permitted s l r then some (next s l r) else none

private def advance : ℕ → List WS → List WS
  | 0, ss => ss
  | n+1, ss => advance n (ss.flatMap succ)

private theorem no_eight_abstract (s : WS) : advance 8 [s] = [] := by
  rcases s with ⟨w,p0,p1,d,r⟩
  fin_cases w <;> fin_cases p0 <;> fin_cases p1 <;> fin_cases d <;>
    fin_cases r <;> decide


attribute [local instance] Classical.propDecidable

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


private abbrev HasMarkP (h : ℕ → LowerPair) (j : ℕ) (right : Bool) : Prop :=
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

private abbrev RunCert (p : LowerPair) : Prop :=
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


private abbrev sh_GoodComp (w : List ℕ+) : Prop :=
  ¬ lowerEnds w [3,1] ∧ ¬ lowerEnds w [1,3,1] ∧ ¬ lowerEnds w [3,1,3,1]
private abbrev sh_HistDec (l : LowerLabel) : Prop :=
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

private noncomputable abbrev Inc (h : ℕ → LowerPair) (j : ℕ) (right : Bool) (l : LowerLabel) :=
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

private noncomputable def absWS (h : ℕ → LowerPair) (j : ℕ) (right done run : Bool) : WS :=
  { wide := wideAt h j right
    p0 := parity (lowerNormalize (h j)).1
    p1 := parity (lowerNormalize (h j)).2
    done := done
    run := run }

private theorem mixed_bits (p : LowerPair) :
    lowerMixed p ↔ (parity (lowerNormalize p).1 != parity (lowerNormalize p).2) = true := by
  classical
  unfold lowerMixed parity lowerNormalize
  split_ifs <;>
    rcases Nat.mod_two_eq_zero_or_one p.1.length with h1|h1 <;>
    rcases Nat.mod_two_eq_zero_or_one p.2.length with h2|h2 <;>
    simp [h1,h2] <;> omega

private theorem permitted_real
    (hf : ∀ p, lowerGood p → lowerParameterBox p →
      let q := lowerNormalize p;
      lowerWidth (q.1++[2]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[3]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[1,1]) < lowerWidth q.2 ∧
      lowerWidth (q.2++[1]) < lowerWidth q.1)
    (h : ℕ → LowerPair) (j : ℕ) (right : Bool) (l : LowerLabel)
    (ho : lowerOffered (h j) l) (hc : h (j+1)=lowerChild (h j) l)
    (hg : lowerGood (h j)) (hbox : lowerParameterBox (h j))
    (dp dc run : Bool) (hrun : run=true → RunCert (h j))
    (hinc : (Inc h j right l=[] ∧ dp=dc) ∨ (dp=false ∧ dc=true ∧ Inc h j right l=[1]))
    (hsix : RelSix l ∧ (l.1=[] → lowerMixed (h j)))
    (rl : RL) (ha : rl.a=l.1.reverse) (hb : rl.b=l.2) :
    permitted (absWS h j right dp run) rl (lowerReflects (h (j+1))) := by
  have hra : rl.a.reverse=rl.a := by cases rl <;> decide
  have hl1 : l.1=rl.a := by
    calc l.1 = l.1.reverse.reverse := by simp
      _ = rl.a.reverse := congrArg List.reverse ha.symm
      _ = rl.a := hra
  have hlab : l=(rl.a,rl.b) := Prod.ext hl1 hb.symm
  have hmix : l.1=[] →
      (parity (lowerNormalize (h j)).1 != parity (lowerNormalize (h j)).2)=true :=
    fun he => (mixed_bits (h j)).mp (hsix.2 he)
  have h23 : rl=.a2 ∨ rl=.a3 → lowerReflects (h (j+1))=true := by
    intro hx
    rw [hc, hlab]
    exact reflect_a23 hf (h j) hg hbox rl hx
  have hb1 : rl=.b1 → lowerReflects (h (j+1))=false := by
    intro hx; subst rl
    rw [hc, hlab]
    exact reflect_b1 hf (h j) hg hbox
  have hrr : rl=.a1 → wideAt h j right=false → run=true →
      lowerReflects (h (j+1))=true := by
    intro hx _ hu; subst rl
    rw [hc, hlab]
    exact reflect_run (h j) (hrun hu)
  cases rl <;> cases hw : wideAt h j right <;> cases dp <;> cases run <;>
    cases hr : lowerReflects (h (j+1)) <;>
    simp_all [permitted, absWS, marked, Inc, RL.a, RL.b, hl1]

private theorem abs_next (h : ℕ → LowerPair) (j : ℕ) (right : Bool)
    (l : LowerLabel) (hc : h (j+1)=lowerChild (h j) l)
    (dp dc run : Bool)
    (rl : RL) (ha : rl.a=l.1.reverse) (hb : rl.b=l.2)
    (hinc : (Inc h j right l=[] ∧ dp=dc) ∨ (dp=false ∧ dc=true ∧ Inc h j right l=[1])) :
    next (absWS h j right dp run) rl (lowerReflects (h (j+1))) =
      absWS h (j+1) right dc
        (next (absWS h j right dp run) rl (lowerReflects (h (j+1)))).run := by
  have hra : rl.a.reverse=rl.a := by cases rl <;> decide
  have hl1 : l.1=rl.a := by
    calc l.1 = l.1.reverse.reverse := by simp
      _ = rl.a.reverse := congrArg List.reverse ha.symm
      _ = rl.a := hra
  have hlab : l=(rl.a,rl.b) := Prod.ext hl1 hb.symm
  simp only [next, absWS, WS.mk.injEq]
  refine ⟨(wide_next h j right l hc).symm, ?_, ?_, ?_⟩
  · have hnrm := normalize_reflect (h (j+1))
    rw [hnrm, hc, hlab]
    cases hr : lowerReflects (lowerChild (h j) (rl.a,rl.b)) <;>
      simp [next, absWS, raw0, raw1, hr, lowerChild, par_append, bitlen, RL.a, RL.b] <;> rfl
  · have hnrm := normalize_reflect (h (j+1))
    rw [hnrm, hc, hlab]
    cases hr : lowerReflects (lowerChild (h j) (rl.a,rl.b)) <;>
      simp [next, absWS, raw0, raw1, hr, lowerChild, par_append, bitlen, RL.a, RL.b] <;> rfl
  · cases rl <;> cases hw : wideAt h j right <;> cases dp <;> cases dc <;>
      simp_all [next, absWS, marked, Inc, RL.a, RL.b]

private theorem next_run_cert
    (hf : ∀ p, lowerGood p → lowerParameterBox p →
      let q := lowerNormalize p;
      lowerWidth (q.1++[2]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[3]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[1,1]) < lowerWidth q.2 ∧
      lowerWidth (q.2++[1]) < lowerWidth q.1)
    (h : ℕ → LowerPair) (j : ℕ) (right : Bool) (l : LowerLabel)
    (hc : h (j+1)=lowerChild (h j) l)
    (hg : lowerGood (h j)) (hbox : lowerParameterBox (h j))
    (dp run : Bool) (rl : RL) (ha : rl.a=l.1.reverse) (hb : rl.b=l.2)
    (hn : (next (absWS h j right dp run) rl (lowerReflects (h (j+1)))).run=true) :
    RunCert (h (j+1)) := by
  have hra : rl.a.reverse=rl.a := by cases rl <;> decide
  have hl1 : l.1=rl.a := by
    calc l.1 = l.1.reverse.reverse := by simp
      _ = rl.a.reverse := congrArg List.reverse ha.symm
      _ = rl.a := hra
  have hlab : l=(rl.a,rl.b) := Prod.ext hl1 hb.symm
  unfold next absWS at hn
  dsimp at hn
  rcases rl <;> cases hw : wideAt h j right <;>
    cases hr : lowerReflects (h (j+1)) <;> simp [hw,hr] at hn
  have hr' : lowerReflects (lowerChild (h j) (RL.a1.a,RL.a1.b))=false := by
    simpa [hc, hlab] using hr
  unfold RunCert
  rw [hc, hlab, normalize_reflect, hr']
  have hi := (hf (h j) hg hbox).2.2.1
  refine ⟨(lowerNormalize (h j)).1, (lowerNormalize (h j)).2, ?_, hi⟩
  simp [lowerChild, RL.a, RL.b]

private theorem mem_succ (s : WS) (l : RL) (r : Bool) (hp : permitted s l r) :
    next s l r ∈ succ s := by
  cases l <;> cases r <;> simp_all [succ, RL.all]

private def reach : ℕ → WS → List WS
  | 0,s => [s]
  | k+1,s => (reach k s).flatMap succ

private theorem no_eight_reach (s : WS) : reach 8 s=[] := by
  rcases s with ⟨w,p0,p1,d,r⟩
  fin_cases w <;> fin_cases p0 <;> fin_cases p1 <;> fin_cases d <;>
    fin_cases r <;> decide

private theorem real_reach
    (hf : ∀ p, lowerGood p → lowerParameterBox p →
      let q := lowerNormalize p;
      lowerWidth (q.1++[2]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[3]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[1,1]) < lowerWidth q.2 ∧
      lowerWidth (q.2++[1]) < lowerWidth q.1)
    (t : ℝ) (h : ℕ → LowerPair) (N : ℕ) (hh : lowerHistory t h N)
    (right : Bool) (start k : ℕ) (hbound : start+k ≤ N)
    (hpersist : ∀ i, i≤k → HasMarkP h (start+i) right) :
    ∃ run : Bool,
      absWS h (start+k) right (doneAt h (start+k) right) run ∈
        reach k (absWS h start right (doneAt h start right) false) ∧
      (run=true → RunCert (h (start+k))) := by
  induction k with
  | zero =>
      refine ⟨false, ?_, by simp⟩
      simp [reach]
  | succ k ih =>
      have hcur : start+k ≤ N := by omega
      obtain ⟨run, hmem, hrun⟩ := ih hcur (fun i hi => hpersist i (by omega))
      have hjlt : start+k < N := by omega
      obtain ⟨l,ho,_,hc⟩ := hh.2.2 (start+k) hjlt
      have hst := hh.2.1 (start+k) hcur
      have hst' := hh.2.1 (start+k+1) (by omega)
      have hp := mark_done h (start+k) right (hpersist k (by omega))
      have hn := mark_done h (start+k+1) right (hpersist (k+1) (by omega))
      let dp := doneAt h (start+k) right
      let dc := doneAt h (start+k+1) right
      have hinc := step_mark_info h (start+k) right l ho hc dp dc hp hn hst'.1
      have hsix := step_six h (start+k) right l ho dp dc hp hinc
      obtain ⟨rl,ha,hb⟩ := rl_of_six hsix.1
      let sn := next (absWS h (start+k) right dp run) rl
        (lowerReflects (h (start+k+1)))
      have hperm := permitted_real hf h (start+k) right l ho hc hst.2.1 hst.2.2.2
        dp dc run hrun hinc hsix rl ha hb
      have hsn : sn ∈ succ (absWS h (start+k) right dp run) := mem_succ _ _ _ hperm
      have hreach : sn ∈ reach (k+1) (absWS h start right (doneAt h start right) false) := by
        simp only [reach, List.mem_flatMap]
        exact ⟨_, hmem, hsn⟩
      have heq := abs_next h (start+k) right l hc dp dc run rl ha hb hinc
      refine ⟨sn.run, ?_, ?_⟩
      · simpa [sn, dp, dc, Nat.add_assoc] using heq ▸ hreach
      · intro hrs
        exact next_run_cert hf h (start+k) right l hc hst.2.1 hst.2.2.2
          dp run rl ha hb (by simpa [sn] using hrs)

private theorem no_eight_real
    (hf : ∀ p, lowerGood p → lowerParameterBox p →
      let q := lowerNormalize p;
      lowerWidth (q.1++[2]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[3]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[1,1]) < lowerWidth q.2 ∧
      lowerWidth (q.2++[1]) < lowerWidth q.1)
    (t : ℝ) (h : ℕ → LowerPair) (N : ℕ) (hh : lowerHistory t h N)
    (right : Bool) (start : ℕ) (hbound : start+8≤N)
    (hpersist : ∀ i, i≤8 → HasMarkP h (start+i) right) : False := by
  obtain ⟨run,hm,-⟩ := real_reach hf t h N hh right start 8 hbound hpersist
  rw [no_eight_reach] at hm
  simpa using hm

private noncomputable def localAt (h : ℕ → LowerPair) (j : ℕ) (right : Bool) : Bool :=
  !(wideAt h j right)

private theorem local_parent (h : ℕ → LowerPair) (j : ℕ) (right : Bool) :
    lowerSide (lowerNormalize (h j)) (localAt h j right) =
      lowerSide (lowerPhysicalPath h j) right := by
  rw [phys_norm_side]
  cases hw : wideAt h j right <;> simp [localAt, hw, lowerSide]

private theorem local_child (h : ℕ → LowerPair) (j : ℕ) (right : Bool)
    (l : LowerLabel) (hc : h (j+1)=lowerChild (h j) l) :
    lowerSide (lowerChild (h j) l) (localAt h j right) =
      lowerSide (lowerPhysicalPath h (j+1)) right := by
  rw [marked_increment h j right l hc]
  cases hw : wideAt h j right <;>
    simp [localAt, hw, lowerSide, lowerChild]
  all_goals symm
  all_goals simpa [hw, lowerSide] using phys_norm_side h j right

private theorem star_child_has_parent_mark (A B : List ℕ+)
    (hc : lowerEnds (A++B) [3,1,3,1])
    (hn31 : ¬ lowerEnds B [3,1]) (hn131 : ¬ lowerEnds B [1,3,1])
    (hn3131 : ¬ lowerEnds B [3,1,3,1]) : HasMark A := by
  have hr : ([1,3,1,3] : List ℕ+) <+: B.reverse++A.reverse := by
    simpa using List.reverse_prefix.mpr hc
  rcases sf_pre4 B.reverse A.reverse hr with hx | ⟨hx,-⟩ | ⟨hx,ha⟩ | ⟨hx,-⟩ | ⟨hx,-⟩
  · exact absurd (List.reverse_prefix.mp (by simpa using hx)) hn3131
  · right
    have hb : B=[] := by simpa using congrArg List.reverse hx
    simpa [hb] using hc
  · left
    change ([3,1,3] : List ℕ+).IsSuffix A
    exact List.reverse_prefix.mp (show ([3,1,3] : List ℕ+).reverse <+: A.reverse from ha)
  · exfalso
    apply hn31
    have hb : B=[3,1] := by simpa using congrArg List.reverse hx
    rw [hb]
    exact ⟨[],rfl⟩
  · exfalso
    apply hn131
    have hb : B=[1,3,1] := by simpa using congrArg List.reverse hx
    rw [hb]
    exact ⟨[],rfl⟩

private theorem history_mono (t : ℝ) (h : ℕ → LowerPair) {a b : ℕ}
    (hh : lowerHistory t h b) (hab : a≤b) : lowerHistory t h a := by
  exact ⟨hh.1, (fun j hj => hh.2.1 j (le_trans hj hab)),
    (fun j hj => hh.2.2 j (lt_of_lt_of_le hj hab))⟩

private theorem boundary_birth
    (hb : ∀ t h n, lowerHistory t h n →
      ∀ l, lowerOffered (h n) l → ∀ right,
      lowerEnds (lowerSide (lowerChild (h n) l) right) [3,1,3] →
      lowerSide (lowerChild (h n) l) right ≠ lowerSide (lowerNormalize (h n)) right →
      l=([2],[3]))
    (t : ℝ) (h : ℕ → LowerPair) (N m : ℕ) (hh : lowerHistory t h N)
    (hm : 0<m) (hmN : m≤N) (right : Bool)
    (hnew : HasMarkP h m right) (hold : ¬ HasMarkP h (m-1) right) :
    h m=lowerChild (h (m-1)) ([2],[3]) ∧
      lowerEnds (lowerSide (lowerPhysicalPath h m) right) [3,1,3] := by
  have hjlt : m-1<N := by omega
  obtain ⟨l,ho,_,hc⟩ := hh.2.2 (m-1) hjlt
  have hm_eq : m-1+1=m := by omega
  rw [hm_eq] at hc
  have hc0 : h (m-1+1)=lowerChild (h (m-1)) l := by simpa [hm_eq] using hc
  let A := lowerSide (lowerPhysicalPath h (m-1)) right
  let B := Inc h (m-1) right l
  have hi := marked_increment h (m-1) right l hc0
  rw [hm_eq] at hi
  have hd := component_data (h (m-1)) l ho
  have hB :
      (¬ lowerEnds B [3,1] ∧ ¬ lowerEnds B [1,3,1] ∧ ¬ lowerEnds B [3,1,3,1]) := by
    cases hw : wideAt h (m-1) right
    · simpa [B,Inc,hw] using ⟨hd.2.1,hd.2.2.1,hd.2.2.2.2.1⟩
    · simpa [B,Inc,hw] using ⟨hd.1.1,hd.1.2.1,hd.1.2.2.2.1⟩
  have hnstar : ¬ lowerEnds (lowerSide (lowerPhysicalPath h m) right) [3,1,3,1] := by
    intro hs
    apply hold
    have hs' := hs
    rw [hi] at hs'
    have : HasMark A := star_child_has_parent_mark A B (by simpa [A,B] using hs')
      hB.1 hB.2.1 hB.2.2
    simpa [HasMarkP,A] using this
  have h313 : lowerEnds (lowerSide (lowerPhysicalPath h m) right) [3,1,3] :=
    hnew.resolve_right hnstar
  have hBne : B≠[] := by
    intro he
    apply hold
    left
    have hx := h313
    rw [hi] at hx
    simpa [B,he] using hx
  let rloc := localAt h (m-1) right
  have hchild : lowerEnds (lowerSide (lowerChild (h (m-1)) l) rloc) [3,1,3] := by
    have hlc := local_child h (m-1) right l hc0
    rw [hm_eq] at hlc
    rw [hlc]
    exact h313
  have hchanged : lowerSide (lowerChild (h (m-1)) l) rloc ≠
      lowerSide (lowerNormalize (h (m-1))) rloc := by
    intro he
    apply hBne
    have hcside := local_child h (m-1) right l hc0
    have hpside := local_parent h (m-1) right
    have happ := marked_increment h (m-1) right l hc0
    rw [← hcside, he, hpside] at happ
    have hlen := congrArg List.length happ
    have hz : B.length=0 := by simpa using hlen
    match B with
    | [] => rfl
    | _::_ => simp at hz
  have hlab := hb t h (m-1) (history_mono t h hh (by omega)) l ho rloc hchild hchanged
  subst l
  exact ⟨hc, h313⟩

theorem solution
    (hf : ∀ p, lowerGood p → lowerParameterBox p →
      let q := lowerNormalize p;
      lowerWidth (q.1++[2]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[3]) < lowerWidth q.2 ∧
      lowerWidth (q.1++[1,1]) < lowerWidth q.2 ∧
      lowerWidth (q.2++[1]) < lowerWidth q.1)
    (hb : ∀ t h n, lowerHistory t h n →
      ∀ l, lowerOffered (h n) l → ∀ right,
      lowerEnds (lowerSide (lowerChild (h n) l) right) [3,1,3] →
      lowerSide (lowerChild (h n) l) right ≠ lowerSide (lowerNormalize (h n)) right →
      l=([2],[3]))
    (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n) :
    lowerBoundedHistory h n := by
  classical
  intro right hend
  let P : ℕ → Prop := fun m => m≤n ∧
    ∀ j, m≤j → j≤n → HasMarkP h j right
  have hex : ∃ m, P m := by
    refine ⟨n, le_rfl, ?_⟩
    intro j hj hjn
    have hjn' : j=n := by omega
    subst j
    exact Or.inr hend
  let m := Nat.find hex
  have hPm : P m := Nat.find_spec hex
  have hmN : m≤n := hPm.1
  have hkeep : ∀ j, m≤j → j≤n → HasMarkP h j right := hPm.2
  have hspan : n-m≤7 := by
    by_contra hn7
    have hm8 : m+8≤n := by omega
    apply no_eight_real hf t h n hh right m hm8
    intro i hi
    exact hkeep (m+i) (by omega) (by omega)
  refine ⟨m, hmN, hspan, ?_, ?_⟩
  · by_cases hm0 : m=0
    · exact Or.inl hm0
    · right
      have hmpos : 0<m := Nat.pos_of_ne_zero hm0
      have hold : ¬ HasMarkP h (m-1) right := by
        intro hp
        have hpred : m-1<m := by omega
        have hlt : m-1 < Nat.find hex := by simpa only [m] using hpred
        have hnP : ¬ P (m-1) := Nat.find_min hex hlt
        apply hnP
        refine ⟨by omega, ?_⟩
        intro j hj hjn
        by_cases hjm : m≤j
        · exact hkeep j hjm hjn
        · have hjp : j=m-1 := by omega
          simpa [hjp] using hp
      obtain ⟨hchild,hsuf⟩ := boundary_birth hb t h n m hh hmpos hmN right
        (hkeep m le_rfl hmN) hold
      exact ⟨hmpos,hchild,hsuf⟩
  · intro j hmj hjn
    exact hkeep j hmj hjn

#print axioms solution
