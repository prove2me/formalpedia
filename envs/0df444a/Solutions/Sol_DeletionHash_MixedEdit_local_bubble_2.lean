-- Prove2me | solution 2 for DeletionHash.MixedEdit.local_bubble
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:11:22.939702+00:00
-- url     : https://prove2.me/submissions/7481b3a9-5a26-43b2-bea7-2b1421a3ead5

import Definitions.Def_DeletionHash_MixedEdit_Bubbles
import Definitions.Def_DeletionHash_MixedEdit_Edits
import Definitions.Def_DeletionHash_MixedEdit_Paths
import Definitions.Def_DeletionHash_MixedEdit_Regime
import Definitions.Def_DeletionHash_MixedEdit_SourceTrace
import Definitions.Def_DeletionHash_MixedEdit_UniqueWords
import Mathlib
import Theorems.Thm_DeletionHash_MixedEdit_shared_source_letters

/- Adapted from Eyal En Gad, deletion-codes-lean, commit 24d093a4 (Apache-2.0). Alphabet generalization preserves the original reconstruction proof. -/
namespace DeletionGraph.OverlapCollision
variable (α : Type*) [Fintype α]
abbrev Bits (n : ℕ) := Fin n → α
def padBits {n : ℕ} (x : Bits α n) (i : ℕ) : Option α :=
  if hi : i < n then some (x ⟨i, hi⟩) else none
def Agree (p : ℕ → Option α) (a : ℕ) (q : ℕ → Option α) (b k : ℕ) : Prop :=
  ∀ i, i < k → p (a+i) = q (b+i)

end DeletionGraph.OverlapCollision
namespace DeletionGraph.UniqueWordCount
open OverlapCollision
variable (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α]
attribute [local instance] Classical.propDecidable

def KUnique (p : ℕ → Option α) (n k : ℕ) : Prop :=
  ∀ a b, a+k ≤ n → b+k ≤ n → Agree α p a p b k → a=b
noncomputable def uniqueWords (n k : ℕ) : Finset (Bits α n) := by
  classical
  exact Finset.univ.filter (fun x => KUnique α (padBits α x) n k)


end DeletionGraph.UniqueWordCount
namespace DeletionGraph.UniqueBridge
open DeletionHash.MixedEdit
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

theorem window_as_ofFn {n k a : ℕ} (x : Word α n) (ha : a+k ≤ n) :
    window k (letters x) a = List.ofFn (fun i : Fin k => x ⟨a+i.val, by omega⟩) := by
  apply List.ext_getElem
  · simp only [window, letters, List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro i hi hj
    simp only [window, letters, List.getElem_take, List.getElem_drop, List.getElem_ofFn]

theorem window_eq_iff {n k a b : ℕ} (x : Word α n)
    (ha : a+k ≤ n) (hb : b+k ≤ n) :
    window k (letters x) a = window k (letters x) b ↔
      OverlapCollision.Agree α (OverlapCollision.padBits α x) a
        (OverlapCollision.padBits α x) b k := by
  rw [window_as_ofFn x ha, window_as_ofFn x hb, List.ofFn_inj]
  constructor
  · intro h i hi
    have he := congrFun h (⟨i, hi⟩ : Fin k)
    simpa only [OverlapCollision.padBits, dif_pos (show a+i<n by omega),
      dif_pos (show b+i<n by omega), Option.some.injEq] using he
  · intro h
    funext i
    have he := h i.val i.isLt
    simpa only [OverlapCollision.padBits, dif_pos (show a+i.val<n by omega),
      dif_pos (show b+i.val<n by omega), Option.some.injEq] using he

theorem unique_iff {n k : ℕ} (x : Word α n) :
    IsUnique k (letters x) ↔ UniqueWordCount.KUnique α (OverlapCollision.padBits α x) n k := by
  unfold IsUnique windows starts
  rw [List.nodup_map_iff_inj_on List.nodup_range]
  simp only [List.mem_range, letters, List.length_ofFn]
  constructor
  · intro h a b ha hb hab
    have hkn : k ≤ n := by omega
    apply h a (by simp only [if_pos hkn]; omega) b (by simp only [if_pos hkn]; omega)
    exact (window_eq_iff x ha hb).mpr hab
  · intro h a ha b hb hab
    by_cases hkn : k ≤ n
    · simp only [if_pos hkn] at ha hb
      exact h a b (by omega) (by omega) ((window_eq_iff x (by omega) (by omega)).mp hab)
    · simp only [if_neg hkn] at ha
      omega

theorem family_eq (n k : ℕ) : uniqueFamily α n k = UniqueWordCount.uniqueWords α n k := by
  classical
  ext x
  simp only [uniqueFamily, UniqueWordCount.uniqueWords, Finset.mem_filter,
    Finset.mem_univ, true_and, unique_iff]

end DeletionGraph.UniqueBridge
namespace DeletionGraph.SourceLetters
open DeletionHash.MixedEdit
universe u
variable {α : Type u}

theorem common_block (m k b i j a c u v : ℕ) (hu : u ≤ b) (hv : v ≤ b)
    (hm : 3*k+2*b ≤ m) :
    ∃ o, o+k ≤ m ∧ (i+o+k ≤ a ∨ a+u ≤ i+o) ∧
      (j+o+k ≤ c ∨ c+v ≤ j+o) := by
  by_cases h0 : (i+k ≤ a ∨ a+u ≤ i) ∧ (j+k ≤ c ∨ c+v ≤ j)
  · exact ⟨0, by omega, by simpa using h0.1, by simpa using h0.2⟩
  by_cases h1 : (i+(k+b)+k ≤ a ∨ a+u ≤ i+(k+b)) ∧
      (j+(k+b)+k ≤ c ∨ c+v ≤ j+(k+b))
  · exact ⟨k+b, by omega, h1⟩
  refine ⟨2*(k+b), by omega, ?_⟩
  omega

theorem edited_length (x : List α) (e : Edit α) (he : e.position+e.removed ≤ x.length) :
    (applyEdit e x).length = e.position+e.replacement.length+(x.length-(e.position+e.removed)) := by
  simp [applyEdit, List.length_take, Nat.min_eq_left (show e.position ≤ x.length by omega), Nat.add_assoc]

theorem word_before (x : List α) (e : Edit α) (he : e.position+e.removed ≤ x.length)
    (a : ℕ) (ha : a < e.position) : (applyEdit e x)[a]? = x[a]? := by
  simp [applyEdit, List.getElem?_append, List.getElem?_take,
    Nat.min_eq_left (show e.position ≤ x.length by omega), ha]

theorem word_after (x : List α) (e : Edit α) (he : e.position+e.removed ≤ x.length)
    (a : ℕ) (ha : e.position+e.replacement.length ≤ a) :
    (applyEdit e x)[a]? = x[a-e.replacement.length+e.removed]? := by
  have hp : e.position ≤ x.length := by omega
  simp only [applyEdit, List.getElem?_append, List.length_append, List.length_take,
    Nat.min_eq_left hp, if_neg (show ¬ a < e.position+e.replacement.length by omega),
    List.getElem?_drop]
  congr 1
  omega

theorem trace_before (x : List α) (e : Edit α) (a : ℕ) (ha : a < e.position) :
    (sourceTrace x (some e))[a]? = some (some a) := by
  simp [sourceTrace, List.getElem?_append, List.getElem?_map, ha]

theorem trace_after (x : List α) (e : Edit α) (he : e.position+e.removed ≤ x.length)
    (a : ℕ) (ha : e.position+e.replacement.length ≤ a)
    (hb : a < (applyEdit e x).length) :
    (sourceTrace x (some e))[a]? = some (some (a-e.replacement.length+e.removed)) := by
  rw [edited_length x e he] at hb
  simp only [sourceTrace, List.getElem?_append, List.length_append, List.length_map,
    List.length_range, List.length_replicate,
    if_neg (show ¬ a < e.position+e.replacement.length by omega), List.getElem?_map]
  simp [List.getElem?_range', show a-(e.position+e.replacement.length) <
    x.length-(e.position+e.removed) by omega]
  omega


def cut (e : Option (Edit α)) : ℕ := e.elim 0 Edit.position
def newLength (e : Option (Edit α)) : ℕ := e.elim 0 (fun e => e.replacement.length)

theorem original_block (x : List α) (e : Option (Edit α)) (b a k : ℕ)
    (he : ValidOne b x e) (ha : a+k ≤ (oneWord x e).length)
    (hside : a+k ≤ cut e ∨ cut e+newLength e ≤ a) :
    ∃ s, s+k ≤ x.length ∧ ∀ h, h < k →
      (oneWord x e)[a+h]? = x[s+h]? ∧
      (sourceTrace x e)[a+h]? = some (some (s+h)) := by
  cases e with
  | none =>
    refine ⟨a, ha, ?_⟩
    intro h hh
    exact ⟨rfl, by simp [sourceTrace, show a+h < x.length by simpa [oneWord] using (show a+h < (oneWord x none).length by omega)]⟩
  | some e =>
    change ValidEdit b x e at he
    have he0 := he.1
    change a+k ≤ (applyEdit e x).length at ha
    change a+k ≤ e.position ∨ e.position+e.replacement.length ≤ a at hside
    rcases hside with hside | hside
    · refine ⟨a, by omega, ?_⟩
      intro h hh
      exact ⟨word_before x e he.1 (a+h) (by omega), trace_before x e (a+h) (by omega)⟩
    · refine ⟨a-e.replacement.length+e.removed, ?_, ?_⟩
      · rw [edited_length x e he.1] at ha
        omega
      · intro h hh
        have hid : a+h-e.replacement.length+e.removed =
            (a-e.replacement.length+e.removed)+h := by omega
        constructor
        · change (applyEdit e x)[a+h]? = _
          rw [word_after x e he.1 (a+h) (by omega), hid]
        · rw [trace_after x e he.1 (a+h) (by omega) (by omega), hid]

theorem trace_position (x : List α) (e : Edit α) (p s : ℕ)
    (h : (sourceTrace x (some e))[p]? = some (some s)) :
    (p < e.position ∧ s=p) ∨
      (e.position+e.replacement.length ≤ p ∧ s=p-e.replacement.length+e.removed) := by
  by_cases hp : p < e.position
  · rw [trace_before x e p hp] at h
    exact Or.inl ⟨hp, (Option.some.inj (Option.some.inj h)).symm⟩
  · right
    by_cases hn : p < e.position+e.replacement.length
    · simp [sourceTrace, List.getElem?_append, hp,
        show p-e.position < e.replacement.length by omega] at h
    · refine ⟨by omega, ?_⟩
      simp only [sourceTrace, List.getElem?_append, List.length_append, List.length_map,
        List.length_range, List.length_replicate, if_neg hn, List.getElem?_map] at h
      simp [Option.map_eq_some_iff] at h
      obtain ⟨hb, hv⟩ := List.getElem?_eq_some_iff.mp h
      simp only [List.getElem_range'] at hv
      omega

theorem trace_injective (x : List α) (e : Option (Edit α)) (p q s : ℕ)
    (hp : (sourceTrace x e)[p]? = some (some s))
    (hq : (sourceTrace x e)[q]? = some (some s)) : p=q := by
  cases e with
  | none =>
    simp [sourceTrace, Option.map_eq_some_iff] at hp hq
    obtain ⟨hp', hvp⟩ := List.getElem?_eq_some_iff.mp hp
    obtain ⟨hq', hvq⟩ := List.getElem?_eq_some_iff.mp hq
    simp only [List.getElem_range] at hvp hvq
    omega
  | some e =>
    have h1 := trace_position x e p s hp
    have h2 := trace_position x e q s hq
    omega


theorem newLength_le (x : List α) (e : Option (Edit α)) (b : ℕ)
    (he : ValidOne b x e) : newLength e ≤ b := by
  cases e with
  | none => simp [newLength]
  | some e => exact he.2.2.1


end DeletionGraph.SourceLetters
namespace DeletionGraph.EditedPrefix
open DeletionHash.MixedEdit SourceLetters UniqueBridge
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

theorem prefix_get {x y : List α} {l i : ℕ} (h : x.take l = y.take l) (hi : i < l) :
    x[i]? = y[i]? := by
  have hg := congrArg (fun z : List α => z[i]?) h
  simpa [hi] using hg

theorem word_new (x : List α) (e : Edit α) (he : e.position+e.removed ≤ x.length)
    (i : ℕ) (hi : i < e.replacement.length) :
    (applyEdit e x)[e.position+i]? = e.replacement[i]? := by
  have hp : e.position ≤ x.length := by omega
  simp [applyEdit, List.getElem?_append, Nat.min_eq_left hp,
    show ¬ e.position+i < e.position by omega, hi]

theorem prefix_bound {n k b : ℕ} (x : Word α n) (hx : IsUnique k (letters x))
    (e : Edit α) (he : ValidEdit b (letters x) e) (l : ℕ)
    (hlx : l ≤ n) (hly : l ≤ (applyEdit e (letters x)).length)
    (hpref : (letters x).take l = (applyEdit e (letters x)).take l) :
    l < e.position+k+b := by
  by_contra hbound
  have hu := he.2.1
  have hv := he.2.2.1
  have hpos : e.position+e.removed ≤ n := by simpa [letters] using he.1
  have hylen := edited_length (letters x) e he.1
  rw [show (letters x).length=n by simp [letters]] at hylen
  let a := e.position+b
  let c := a-e.replacement.length+e.removed
  have ha : a+k ≤ n := by dsimp [a]; omega
  have hc : c+k ≤ n := by dsimp [c,a]; omega
  have hac : a=c := by
    apply (unique_iff x).mp hx a c ha hc
    intro i hi
    have hidx : a+i-e.replacement.length+e.removed = c+i := by dsimp [a,c]; omega
    have hg := prefix_get hpref (show a+i<l by dsimp [a]; omega)
    rw [word_after (letters x) e he.1 (a+i) (by dsimp [a]; omega), hidx] at hg
    simpa [OverlapCollision.padBits, letters, show a+i<n by omega, show c+i<n by omega] using hg
  have huv : e.removed=e.replacement.length := by dsimp [a,c] at hac; omega
  apply he.2.2.2
  apply List.ext_getElem
  · simp only [window, List.length_take, List.length_drop, letters, List.length_ofFn]
    omega
  · intro i hi hj
    have hidx : e.position+i < (letters x).length := by
      simp only [letters, List.length_ofFn]
      omega
    have hg := prefix_get hpref (show e.position+i<l by omega)
    rw [word_new (letters x) e he.1 i hj] at hg
    simp only [window, List.getElem_take, List.getElem_drop]
    simpa only [List.getElem?_eq_getElem hidx, List.getElem?_eq_getElem hj,
      Option.some.injEq] using hg

end DeletionGraph.EditedPrefix
namespace DeletionGraph.EditedSuffix
open DeletionHash.MixedEdit SourceLetters UniqueBridge EditedPrefix
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

theorem suffix_bound {n k b : ℕ} (x : Word α n) (hx : IsUnique k (letters x))
    (e : Edit α) (he : ValidEdit b (letters x) e) (s : ℕ)
    (hsx : s ≤ n) (hsy : s ≤ (applyEdit e (letters x)).length)
    (hsuff : (letters x).drop (n-s) =
      (applyEdit e (letters x)).drop ((applyEdit e (letters x)).length-s)) :
    s < n-(e.position+e.removed)+k+b := by
  by_contra hbound
  have hu := he.2.1
  have hv := he.2.2.1
  have hpos : e.position+e.removed ≤ n := by simpa [letters] using he.1
  have hylen := edited_length (letters x) e he.1
  rw [show (letters x).length=n by simp [letters]] at hylen
  let a := e.position+e.removed-(k+b)
  let d := e.position+e.replacement.length-(k+b)
  let o := a-(n-s)
  have hfit : k+b ≤ e.position+e.removed ∧ k+b ≤ e.position+e.replacement.length := by omega
  have ha : a+k ≤ e.position := by dsimp [a]; omega
  have hd : d+k ≤ e.position := by dsimp [d]; omega
  have hbase : n-s+o=a := by dsimp [o,a]; omega
  have hbase' : (applyEdit e (letters x)).length-s+o=d := by dsimp [o,a,d]; omega
  have had : a=d := by
    apply (unique_iff x).mp hx a d (by omega) (by omega)
    intro i hi
    have hg := congrArg (fun z : List α => z[o+i]?) hsuff
    have hg' : (letters x)[a+i]? = (applyEdit e (letters x))[d+i]? := by
      simpa only [List.getElem?_drop, ← Nat.add_assoc, hbase, hbase'] using hg
    rw [word_before (letters x) e he.1 (d+i) (by omega)] at hg'
    simpa [OverlapCollision.padBits, letters, show a+i<n by omega, show d+i<n by omega] using hg'
  have huv : e.removed=e.replacement.length := by dsimp [a,d] at had; omega
  have hylen' : (applyEdit e (letters x)).length=n := by omega
  rw [hylen'] at hsuff
  apply he.2.2.2
  apply List.ext_getElem
  · simp only [window, List.length_take, List.length_drop, letters, List.length_ofFn]
    omega
  · intro i hi hj
    have hidx : e.position+i < (letters x).length := by
      simp only [letters, List.length_ofFn]
      omega
    have hg := congrArg (fun z : List α => z[e.position-(n-s)+i]?) hsuff
    have hstart : n-s+(e.position-(n-s)+i)=e.position+i := by omega
    have hg' : (letters x)[e.position+i]? = (applyEdit e (letters x))[e.position+i]? := by
      simpa only [List.getElem?_drop, hstart] using hg
    rw [word_new (letters x) e he.1 i hj] at hg'
    simp only [window, List.getElem_take, List.getElem_drop]
    simpa only [List.getElem?_eq_getElem hidx, List.getElem?_eq_getElem hj,
      Option.some.injEq] using hg'

end DeletionGraph.EditedSuffix
namespace DeletionGraph.EditEndpoints
open DeletionHash.MixedEdit EditedPrefix
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

theorem exists_best (bound : ℕ) (P : ℕ → Prop) (hzero : P 0) :
    ∃ l, l ≤ bound ∧ P l ∧ ∀ j, j ≤ bound → P j → j ≤ l := by
  classical
  let S := (Finset.range (bound+1)).filter P
  have hS : S.Nonempty := ⟨0, by simp [S,hzero]⟩
  have hm := Finset.mem_filter.mp (Finset.max'_mem S hS)
  refine ⟨S.max' hS, ?_, hm.2, ?_⟩
  · have h := Finset.mem_range.mp hm.1
    omega
  · intro j hj hp
    exact Finset.le_max' S j (by simp [S,hp]; omega)

theorem prefix_next (x y : List α) (l : ℕ) (hx : l < x.length) (hy : l < y.length)
    (he : x.take l = y.take l)
    (hmax : ∀ j, j ≤ min x.length y.length → x.take j = y.take j → j ≤ l) :
    x[l]? ≠ y[l]? := by
  intro hnext
  have he' : x.take (l+1) = y.take (l+1) := by
    apply List.ext_getElem
    · simp only [List.length_take]
      omega
    · intro i hi hj
      have hi' : i < l+1 := by
        have h := hi
        simp only [List.length_take] at h
        omega
      have hix : i < x.length := by omega
      have hiy : i < y.length := by omega
      simp only [List.getElem_take]
      have hg : x[i]? = y[i]? := by
        by_cases hil : i < l
        · exact prefix_get he hil
        · have hil : i=l := by omega
          simpa only [hil] using hnext
      simpa only [List.getElem?_eq_getElem hix, List.getElem?_eq_getElem hiy,
        Option.some.injEq] using hg
  have h := hmax (l+1) (by omega) he'
  omega

theorem suffix_prev (x y : List α) (s : ℕ) (hx : s < x.length) (hy : s < y.length)
    (he : x.drop (x.length-s) = y.drop (y.length-s))
    (hmax : ∀ j, j ≤ min x.length y.length →
      x.drop (x.length-j) = y.drop (y.length-j) → j ≤ s) :
    x[x.length-s-1]? ≠ y[y.length-s-1]? := by
  intro hprev
  have he' : x.drop (x.length-(s+1)) = y.drop (y.length-(s+1)) := by
    apply List.ext_getElem
    · simp only [List.length_drop]
      omega
    · intro i hi hj
      have hix : x.length-(s+1)+i < x.length := by
        simp only [List.length_drop] at hi
        omega
      have hiy : y.length-(s+1)+i < y.length := by
        simp only [List.length_drop] at hj
        omega
      simp only [List.getElem_drop]
      have hg : x[x.length-(s+1)+i]? = y[y.length-(s+1)+i]? := by
        by_cases hi0 : i=0
        · subst i
          simpa only [Nat.add_zero, Nat.sub_add_eq] using hprev
        · have h := congrArg (fun z : List α => z[i-1]?) he
          have h1 : x.length-s+(i-1)=x.length-(s+1)+i := by omega
          have h2 : y.length-s+(i-1)=y.length-(s+1)+i := by omega
          simpa only [List.getElem?_drop,h1,h2] using h
      simpa only [List.getElem?_eq_getElem hix, List.getElem?_eq_getElem hiy,
        Option.some.injEq] using hg
  have h := hmax (s+1) (by omega) he'
  omega


structure MatchingEnds (x y : List α) where
  prefixLen : ℕ
  suffixLen : ℕ
  prefix_le : prefixLen ≤ min x.length y.length
  suffix_le : suffixLen ≤ min x.length y.length
  prefix_eq : x.take prefixLen = y.take prefixLen
  suffix_eq : x.drop (x.length-suffixLen) = y.drop (y.length-suffixLen)
  prefix_max : ∀ j, j ≤ min x.length y.length → x.take j = y.take j → j ≤ prefixLen
  suffix_max : ∀ j, j ≤ min x.length y.length →
    x.drop (x.length-j) = y.drop (y.length-j) → j ≤ suffixLen

theorem matchingEnds_exist (x y : List α) : Nonempty (MatchingEnds x y) := by
  obtain ⟨l, hl, he, hm⟩ := exists_best (min x.length y.length)
    (fun j => x.take j=y.take j) (by simp)
  obtain ⟨s, hs, he', hm'⟩ := exists_best (min x.length y.length)
    (fun j => x.drop (x.length-j)=y.drop (y.length-j)) (by simp)
  exact ⟨⟨l,s,hl,hs,he,he',hm,hm'⟩⟩

theorem unchanged_prefix (x : List α) (e : Edit α)
    (he : e.position+e.removed ≤ x.length) :
    x.take e.position = (applyEdit e x).take e.position := by
  have hp : e.position ≤ x.length := by omega
  simp [applyEdit, List.take_append, Nat.min_eq_left hp]

theorem unchanged_suffix (x : List α) (e : Edit α)
    (he : e.position+e.removed ≤ x.length) :
    x.drop (e.position+e.removed) = (applyEdit e x).drop (e.position+e.replacement.length) := by
  have hp : e.position ≤ x.length := by omega
  simp [applyEdit, List.drop_append, Nat.min_eq_left hp]

theorem matchingEnds_bounds {n k b : ℕ} (x : Word α n) (hx : IsUnique k (letters x))
    (e : Edit α) (he : ValidEdit b (letters x) e)
    (ends : MatchingEnds (letters x) (applyEdit e (letters x))) :
    e.position ≤ ends.prefixLen ∧ ends.prefixLen < e.position+k+b ∧
      n-(e.position+e.removed) ≤ ends.suffixLen ∧
      ends.suffixLen < n-(e.position+e.removed)+k+b := by
  have hxlen : (letters x).length=n := by simp [letters]
  have hp : e.position+e.removed ≤ n := by simpa only [hxlen] using he.1
  have hylen := SourceLetters.edited_length (letters x) e he.1
  rw [hxlen] at hylen
  have hl := ends.prefix_le
  have hs := ends.suffix_le
  rw [hxlen] at hl hs
  refine ⟨?_, prefix_bound x hx e he ends.prefixLen (by omega) (by omega) ends.prefix_eq,
    ?_, EditedSuffix.suffix_bound x hx e he ends.suffixLen (by omega) (by omega) ?_⟩
  · apply ends.prefix_max
    · rw [hxlen]
      omega
    · exact unchanged_prefix _ e he.1
  · apply ends.suffix_max
    · rw [hxlen]
      omega
    · rw [hxlen]
      have h1 : n-(n-(e.position+e.removed))=e.position+e.removed := by omega
      have h2 : (applyEdit e (letters x)).length-(n-(e.position+e.removed))=
          e.position+e.replacement.length := by omega
      rw [h1,h2]
      exact unchanged_suffix _ e he.1
  · simpa only [hxlen] using ends.suffix_eq


end DeletionGraph.EditEndpoints
namespace DeletionGraph.LocalIntersection
open DeletionHash.MixedEdit SourceLetters EditEndpoints
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

theorem common_windows {n t b k L : ℕ} (hreg : Regime (Fintype.card α) n t b k L)
    (x : Word α n) (hx : IsUnique k (letters x)) (e : Edit α)
    (he : ValidEdit b (letters x) e) (hleft : 2*(L+b) ≤ e.position)
    (hright : e.position+e.removed+2*(L+b) ≤ n)
    (ends : MatchingEnds (letters x) (applyEdit e (letters x)))
    (i j : ℕ)
    (hi : ends.prefixLen-(L-1) ≤ i ∧ i ≤ n-ends.suffixLen)
    (hj : ends.prefixLen-(L-1) ≤ j ∧ j ≤ (applyEdit e (letters x)).length-ends.suffixLen)
    (hw : window (L-1) (letters x) i = window (L-1) (applyEdit e (letters x)) j) :
    (i=ends.prefixLen-(L-1) ∧ j=ends.prefixLen-(L-1)) ∨
      (i=n-ends.suffixLen ∧ j=(applyEdit e (letters x)).length-ends.suffixLen) := by
  obtain ⟨hq,ht,hb,hk,hL,hbk,hn⟩ := hreg
  have hxu : (letters x).length=n := by simp [letters]
  have hu := he.2.1
  have hv := he.2.2.1
  have hp : e.position+e.removed ≤ n := by simpa only [hxu] using he.1
  have hylen := edited_length (letters x) e he.1
  rw [hxu] at hylen
  obtain ⟨hl0,hl1,hs0,hs1⟩ := matchingEnds_bounds x hx e he ends
  have hpl : ends.prefixLen < n := by omega
  have hpr : ends.prefixLen < (applyEdit e (letters x)).length := by omega
  have hsl : ends.suffixLen < n := by omega
  have hsr : ends.suffixLen < (applyEdit e (letters x)).length := by omega
  have hml : L-1 ≤ ends.prefixLen := by omega
  have hms : L-1 ≤ ends.suffixLen := by omega
  have hwi : i+(L-1) ≤ n := by omega
  have hwj : j+(L-1) ≤ (applyEdit e (letters x)).length := by omega
  obtain ⟨o,ho,hs⟩ := (DeletionHash.MixedEdit.shared_source_letters n t b k L ⟨hq,ht,hb,hk,hL,hbk,hn⟩ x hx).1 none (some e)
    (by trivial) he i j (by simpa only [oneWord,hxu] using hwi) hwj hw
  obtain ⟨s,hsi,hsj⟩ := hs 0 (by omega)
  simp only [Nat.add_zero] at hsi hsj
  have hio : i+o<n := by omega
  have hsrc : i+o=s := by simpa [sourceTrace,hxu,hio] using hsi
  obtain hbefore | hafter := trace_position (letters x) e (j+o) s hsj
  · have hij : i=j := by omega
    have hia : i=ends.prefixLen-(L-1) := by
      by_contra hne
      have hoff : ends.prefixLen-i < L-1 := by omega
      have hidx : i+(ends.prefixLen-i)=ends.prefixLen := by omega
      have hidx' : j+(ends.prefixLen-i)=ends.prefixLen := by omega
      have hg := congrArg (fun z : List α => z[ends.prefixLen-i]?) hw
      have heq : (letters x)[ends.prefixLen]? = (applyEdit e (letters x))[ends.prefixLen]? := by
        simpa [window,hoff,hidx,hidx'] using hg
      exact prefix_next (letters x) (applyEdit e (letters x)) ends.prefixLen
        (by simpa only [hxu] using hpl) hpr ends.prefix_eq ends.prefix_max heq
    exact Or.inl ⟨hia,by omega⟩
  · have hij : i+e.replacement.length=j+e.removed := by omega
    have hcross : n-ends.suffixLen ≤ i+o := by omega
    have halign : n-ends.suffixLen+e.replacement.length =
        (applyEdit e (letters x)).length-ends.suffixLen+e.removed := by omega
    have hic : i=n-ends.suffixLen := by
      by_contra hne
      have hoff : n-ends.suffixLen-1-i < L-1 := by omega
      have hidx : i+(n-ends.suffixLen-1-i)=n-ends.suffixLen-1 := by omega
      have hidx' : j+(n-ends.suffixLen-1-i)=
          (applyEdit e (letters x)).length-ends.suffixLen-1 := by omega
      have hg := congrArg (fun z : List α => z[n-ends.suffixLen-1-i]?) hw
      have heq : (letters x)[n-ends.suffixLen-1]? =
          (applyEdit e (letters x))[(applyEdit e (letters x)).length-ends.suffixLen-1]? := by
        simpa [window,hoff,hidx,hidx'] using hg
      apply suffix_prev (letters x) (applyEdit e (letters x)) ends.suffixLen
        (by simpa only [hxu] using hsl) hsr ends.suffix_eq ends.suffix_max
      simpa only [hxu] using heq
    exact Or.inr ⟨hic,by omega⟩

end DeletionGraph.LocalIntersection
namespace DeletionGraph.SpectrumPath
open DeletionHash.MixedEdit UniqueBridge
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

theorem nonzero_iff_mem (L : ℕ) (x : List α) (g : Gram α L) :
    spectrum L x g ≠ 0 ↔ List.ofFn g ∈ windows L x := by
  simp [DeletionHash.MixedEdit.spectrum, List.count_eq_zero]

theorem windows_mem_iff {n L : ℕ} (x : Word α n) (g : Gram α L) :
    List.ofFn g ∈ windows L (letters x) ↔
      ∃ a, a+L ≤ n ∧ window L (letters x) a = List.ofFn g := by
  unfold windows starts
  simp only [List.mem_map, List.mem_range, letters, List.length_ofFn]
  constructor
  · rintro ⟨a, ha, hg⟩
    by_cases h : L ≤ n
    · simp only [if_pos h] at ha
      exact ⟨a, by omega, hg⟩
    · simp only [if_neg h] at ha
      omega
  · rintro ⟨a, ha, hg⟩
    refine ⟨a, ?_, hg⟩
    rw [if_pos (show L ≤ n by omega)]
    omega

theorem spells {n L : ℕ} (y : Word α n) (hL : 1 ≤ L)
    (hy : IsUnique (L-1) (letters y)) : SpellsSimplePath L (letters y) := by
  refine ⟨hy, ?_, fun g => nonzero_iff_mem L (letters y) g⟩
  intro i hi
  have hiL : i+L ≤ n := by
    simp only [starts, letters, List.length_ofFn, List.mem_range] at hi
    split_ifs at hi <;> omega
  let g : Gram α L := fun j => y ⟨i+j.val, by omega⟩
  refine ⟨g, (window_as_ofFn y hiL).symm, ?_, ?_⟩
  · rw [window_as_ofFn y (show i+(L-1) ≤ n by omega)]
    rfl
  · rw [window_as_ofFn y (show i+1+(L-1) ≤ n by omega)]
    apply congrArg List.ofFn
    funext j
    dsimp [gramSuffix, g]
    congr 1
    apply Fin.ext
    dsimp
    omega


end DeletionGraph.SpectrumPath
namespace DeletionGraph.WindowTools
open DeletionHash.MixedEdit
universe u
variable {α : Type u}

theorem window_window (x : List α) (a h i k : ℕ) (hi : i+k ≤ h) :
    window k (window h x a) i = window k x (a+i) := by
  apply List.ext_getElem
  · simp only [window, List.length_take, List.length_drop]
    omega
  · intro j hj hk
    simp only [window, List.getElem_take, List.getElem_drop, Nat.add_assoc]

theorem window_take (x : List α) (h i k : ℕ) (hi : i+k ≤ h) :
    window k (x.take h) i = window k x i := by
  simpa only [window, List.drop_zero, Nat.zero_add] using window_window x 0 h i k hi

theorem window_of_append (X P Y : List α) :
    window P.length (X++P++Y) X.length = P := by
  simp [window, List.drop_append]

theorem windows_length (k : ℕ) (x : List α) : (windows k x).length = x.length+1-k := by
  simp only [windows, starts, List.length_map, List.length_range]
  split_ifs <;> omega

theorem windows_get (k : ℕ) (x : List α) (i : ℕ) (hi : i < (windows k x).length) :
    (windows k x)[i] = window k x i := by
  simp [windows, starts, List.getElem_map, List.getElem_range]

theorem unique_positions {k : ℕ} {x : List α} :
    IsUnique k x ↔ ∀ a b, a+k ≤ x.length → b+k ≤ x.length →
      window k x a = window k x b → a=b := by
  unfold IsUnique windows starts
  rw [List.nodup_map_iff_inj_on List.nodup_range]
  simp only [List.mem_range]
  constructor
  · intro h a b ha hb he
    have hk : k ≤ x.length := by omega
    apply h a (by rw [if_pos hk]; omega) b (by rw [if_pos hk]; omega) he
  · intro h a ha b hb he
    by_cases hk : k ≤ x.length
    · simp only [if_pos hk] at ha hb
      exact h a b (by omega) (by omega) he
    · simp [hk] at ha

theorem unique_subwindow {k : ℕ} {x : List α} (hx : IsUnique k x)
    (a h : ℕ) (ha : a+h ≤ x.length) : IsUnique k (window h x a) := by
  apply unique_positions.mpr
  intro i j hi hj he
  have hlen : (window h x a).length=h := by
    simp only [window, List.length_take, List.length_drop]
    omega
  rw [hlen] at hi hj
  rw [window_window x a h i k hi, window_window x a h j k hj] at he
  have h := unique_positions.mp hx (a+i) (a+j) (by omega) (by omega) he
  omega

theorem spells_list [Fintype α] [DecidableEq α] [Nonempty α]
    (L : ℕ) (x : List α) (hL : 1 ≤ L) (hx : IsUnique (L-1) x) :
    SpellsSimplePath L x := by
  let y : Word α x.length := fun i => x.get i
  have hy : letters y=x := by simp [letters,y]
  have h := SpectrumPath.spells y hL (by rwa [hy])
  simpa only [hy] using h


theorem first_of_window (x P : List α) (a m : ℕ)
    (he : window P.length x a=P) (hm : m ≤ P.length) :
    P.take m=window m x a := by
  have h := window_window x a P.length 0 m (by omega)
  rw [he] at h
  simpa only [window,List.drop_zero,Nat.add_zero] using h

theorem last_of_window (x P : List α) (a m : ℕ)
    (he : window P.length x a=P) (hm : m ≤ P.length) :
    P.drop (P.length-m)=window m x (a+(P.length-m)) := by
  have h := window_window x a P.length (P.length-m) m (by omega)
  rw [he] at h
  have hd : (P.drop (P.length-m)).length=m := by simp only [List.length_drop]; omega
  have ht : (P.drop (P.length-m)).take m=P.drop (P.length-m) := by
    apply List.take_of_length_le
    omega
  simpa only [window,ht] using h


end DeletionGraph.WindowTools
namespace DeletionGraph.EditFrame
open DeletionHash.MixedEdit WindowTools
universe u
variable {α : Type u}

theorem frame (x : List α) (e : Edit α) (a c : ℕ)
    (ha : a ≤ e.position) (hc : e.position+e.removed ≤ c) (hcn : c ≤ x.length) :
    ∃ A B X Y : List α,
      x=X++A++window e.removed x e.position++B++Y ∧
      applyEdit e x=X++A++e.replacement++B++Y ∧
      X.length=a ∧ A.length=e.position-a ∧ B.length=c-(e.position+e.removed) := by
  let X := x.take a
  let A := window (e.position-a) x a
  let B := window (c-(e.position+e.removed)) x (e.position+e.removed)
  let Y := x.drop c
  have hp : e.position ≤ x.length := by omega
  have hleft : x.take e.position=X++A := by
    have h : x.take (a+(e.position-a))=x.take a++(x.drop a).take (e.position-a) := List.take_add
    have hidx : a+(e.position-a)=e.position := by omega
    simpa only [hidx,X,A,window] using h
  have hright : x.drop (e.position+e.removed)=B++Y := by
    have h := (List.take_append_drop (c-(e.position+e.removed)) (x.drop (e.position+e.removed))).symm
    have hidx : (e.position+e.removed)+(c-(e.position+e.removed))=c := by omega
    simpa only [List.drop_drop,hidx,B,Y,window] using h
  have hmiddle : x.drop e.position =
      window e.removed x e.position ++ x.drop (e.position+e.removed) := by
    simpa only [window,List.drop_drop] using
      (List.take_append_drop e.removed (x.drop e.position)).symm
  have hword : x=x.take e.position++window e.removed x e.position++x.drop (e.position+e.removed) := by
    rw [List.append_assoc,← hmiddle]
    exact (List.take_append_drop e.position x).symm
  refine ⟨A,B,X,Y,?_,?_,?_,?_,?_⟩
  · rw [hleft,hright] at hword
    simpa only [List.append_assoc] using hword
  · simp only [applyEdit,hleft,hright,List.append_assoc]
  · dsimp [X]
    simp only [List.length_take]
    omega
  · dsimp [A]
    simp only [window,List.length_take,List.length_drop]
    omega
  · dsimp [B]
    simp only [window,List.length_take,List.length_drop]
    omega

end DeletionGraph.EditFrame
namespace DeletionGraph.SpectrumContext
open DeletionHash.MixedEdit WindowTools
universe u
variable {α : Type u}

theorem windows_append_left (X P : List α) (m : ℕ) (hm : m ≤ P.length) :
    windows (m+1) (X++P) = windows (m+1) (X++P.take m) ++ windows (m+1) P := by
  have hleft : (windows (m+1) (X++P.take m)).length=X.length := by
    rw [windows_length]
    simp only [List.length_append, List.length_take]
    omega
  apply List.ext_getElem
  · simp only [List.length_append, windows_length, List.length_take]
    omega
  · intro i hi hj
    rw [windows_get]
    by_cases hx : i<X.length
    · have hix : i<(windows (m+1) (X++P.take m)).length := by omega
      rw [List.getElem_append_left hix, windows_get]
      have htake : (X++P).take (X.length+m)=X++P.take m := by
        simp [List.take_append]
      rw [← htake, window_take _ _ _ _ (by omega)]
    · have hix : (windows (m+1) (X++P.take m)).length ≤ i := by omega
      rw [List.getElem_append_right hix, windows_get, hleft]
      have hdrop : X.drop i=[] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_drop]
        omega
      simp [window, List.drop_append, hdrop]

theorem windows_append_right (P Y : List α) (m : ℕ) (hm : m ≤ P.length) :
    windows (m+1) (P++Y) = windows (m+1) P ++
      windows (m+1) (P.drop (P.length-m)++Y) := by
  let A := P.take (P.length-m)
  let S := P.drop (P.length-m)
  have hP : A++S=P := List.take_append_drop _ _
  have hS : S.length=m := by dsimp [S]; simp only [List.length_drop]; omega
  have htake : (S++Y).take m=S := by rw [← hS]; simp
  have h := windows_append_left A (S++Y) m (by simp only [List.length_append,hS]; omega)
  rw [htake] at h
  simpa only [← List.append_assoc,hP,S] using h

theorem windows_context (X P Y : List α) (m : ℕ) (hm : m ≤ P.length) :
    windows (m+1) (X++P++Y) =
      windows (m+1) (X++P.take m) ++ windows (m+1) P ++
        windows (m+1) (P.drop (P.length-m)++Y) := by
  have htake : (P++Y).take m=P.take m := by
    simp [List.take_append, show m-P.length=0 by omega]
  rw [List.append_assoc, windows_append_left X (P++Y) m (by simp only [List.length_append]; omega),
    htake, windows_append_right P Y m hm, List.append_assoc]

theorem spectrum_context [DecidableEq α] (X P Y : List α) (m : ℕ) (hm : m ≤ P.length) :
    spectrum (m+1) (X++P++Y) =
      spectrum (m+1) (X++P.take m) + spectrum (m+1) P +
        spectrum (m+1) (P.drop (P.length-m)++Y) := by
  funext g
  simp only [DeletionHash.MixedEdit.spectrum, windows_context X P Y m hm,
    List.count_append, Nat.cast_add, Pi.add_apply]

theorem context_cancel [DecidableEq α] (X P Q Y : List α) (m : ℕ)
    (hP : m ≤ P.length) (hQ : m ≤ Q.length)
    (hfirst : P.take m=Q.take m)
    (hlast : P.drop (P.length-m)=Q.drop (Q.length-m)) :
    spectrum (m+1) (X++Q++Y)-spectrum (m+1) (X++P++Y) =
      spectrum (m+1) Q-spectrum (m+1) P := by
  rw [spectrum_context X Q Y m hQ,spectrum_context X P Y m hP,hfirst,hlast]
  abel

end DeletionGraph.SpectrumContext
namespace DeletionGraph.LocalBubble
open DeletionHash.MixedEdit

universe u

/-- Lemma 2.4: actual flanks and unchanged exterior, full path and length geometry. -/
theorem construct {α : Type u} [Fintype α] [DecidableEq α]
    (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (x : Word α n) (hx : IsUnique k (letters x)) (e : Edit α)
    (he : ValidEdit b (letters x) e) (hleft : 2*(L+b) ≤ e.position)
    (hright : e.position+e.removed+2*(L+b) ≤ n) :
    let U := window e.removed (letters x) e.position
    ∃ A B X Y : List α,
      letters x = X ++ A ++ U ++ B ++ Y ∧
      applyEdit e (letters x) = X ++ A ++ e.replacement ++ B ++ Y ∧
      e.position = X.length + A.length ∧
      (L-1)-k-b ≤ A.length ∧ A.length ≤ L-1 ∧
      (L-1)-k-b ≤ B.length ∧ B.length ≤ L-1 ∧
      Bubble k L b (A ++ U ++ B) (A ++ e.replacement ++ B) ∧
      spectrum L (applyEdit e (letters x)) - spectrum L (letters x) =
        spectrum L (A ++ e.replacement ++ B) - spectrum L (A ++ U ++ B) := by
  classical
  obtain ⟨hq,ht,hb,hk,hL,hbk,hn⟩ := hreg
  letI : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  let m := L-1
  let y := applyEdit e (letters x)
  let U := window e.removed (letters x) e.position
  obtain ⟨ends⟩ := EditEndpoints.matchingEnds_exist (letters x) y
  obtain ⟨hl0,hl1,hs0,hs1⟩ := EditEndpoints.matchingEnds_bounds x hx e he ends
  have hxlen : (letters x).length=n := by simp [letters]
  have hp : e.position+e.removed ≤ n := by simpa only [hxlen] using he.1
  have hu := he.2.1
  have hv := he.2.2.1
  have hylen : y.length=e.position+e.replacement.length+(n-(e.position+e.removed)) := by
    simpa only [hxlen] using SourceLetters.edited_length (letters x) e he.1
  have hm : m=3*k+3*b+2 := by dsimp [m]; omega
  have hLm : L=m+1 := by omega
  have hlm : m ≤ ends.prefixLen := by omega
  have hsm : m ≤ ends.suffixLen := by omega
  have hsl : ends.suffixLen < n := by omega
  have hsr : ends.suffixLen < y.length := by omega
  let a := ends.prefixLen-m
  let c := n-ends.suffixLen
  let d := y.length-ends.suffixLen
  have haeq : a+m=ends.prefixLen := by dsimp [a]; omega
  have hceq : c+ends.suffixLen=n := by dsimp [c]; omega
  have hdeq : d+ends.suffixLen=y.length := by dsimp [d]; omega
  have ha : a ≤ e.position := by omega
  have hc : e.position+e.removed ≤ c+m := by omega
  have hcn : c+m ≤ n := by omega
  have hdn : d+m ≤ y.length := by omega
  have hU : U.length=e.removed := by
    dsimp [U]
    simp only [window,List.length_take,List.length_drop,hxlen]
    omega
  obtain ⟨A,B,X,Y,hframe,hframe',hX,hA,hB⟩ :=
    EditFrame.frame (letters x) e a (c+m) ha hc (by simpa only [hxlen] using hcn)
  let P := A++U++B
  let Q := A++e.replacement++B
  have hword : letters x=X++P++Y := by simpa only [P,U,List.append_assoc] using hframe
  have hword' : y=X++Q++Y := by simpa only [Q,List.append_assoc] using hframe'
  have hAlow : m-k-b ≤ A.length := by omega
  have hAup : A.length ≤ m := by omega
  have hBlow : m-k-b ≤ B.length := by omega
  have hBup : B.length ≤ m := by omega
  have hPlen : P.length=c+m-a := by simp only [P,List.length_append,hU]; omega
  have hQlen : Q.length=d+m-a := by simp only [Q,List.length_append]; omega
  have hPlow : L ≤ P.length := by simp only [P,List.length_append]; omega
  have hQlow : L ≤ Q.length := by simp only [Q,List.length_append]; omega
  have hPup : P.length ≤ 2*m+b := by simp only [P,List.length_append]; omega
  have hQup : Q.length ≤ 2*m+b := by simp only [Q,List.length_append]; omega
  have hPm : m ≤ P.length := by omega
  have hQm : m ≤ Q.length := by omega
  have hP : window P.length (letters x) a=P := by
    rw [hword,← hX]
    exact WindowTools.window_of_append X P Y
  have hQ : window Q.length y a=Q := by
    rw [hword',← hX]
    exact WindowTools.window_of_append X Q Y
  have hfirstP := WindowTools.first_of_window (letters x) P a m hP hPm
  have hfirstQ := WindowTools.first_of_window y Q a m hQ hQm
  have hfirst : P.take m=Q.take m := by
    rw [hfirstP,hfirstQ]
    calc
      window m (letters x) a = window m ((letters x).take ends.prefixLen) a :=
        (WindowTools.window_take _ _ _ _ (by omega)).symm
      _ = window m (y.take ends.prefixLen) a := congrArg (fun z => window m z a) ends.prefix_eq
      _ = window m y a := WindowTools.window_take _ _ _ _ (by omega)
  have hlastP : P.drop (P.length-m)=window m (letters x) c := by
    have h := WindowTools.last_of_window (letters x) P a m hP hPm
    have heq : a+(P.length-m)=c := by omega
    simpa only [heq] using h
  have hlastQ : Q.drop (Q.length-m)=window m y d := by
    have h := WindowTools.last_of_window y Q a m hQ hQm
    have heq : a+(Q.length-m)=d := by omega
    simpa only [heq] using h
  have hlast : P.drop (P.length-m)=Q.drop (Q.length-m) := by
    rw [hlastP,hlastQ]
    have h := congrArg (List.take m) ends.suffix_eq
    simpa only [window,hxlen,c,d] using h
  have hxm : IsUnique m (letters x) := by
    simpa only [oneWord] using (DeletionHash.MixedEdit.shared_source_letters n t b k L ⟨hq,ht,hb,hk,hL,hbk,hn⟩ x hx).2 none (by trivial)
  have hym : IsUnique m y := (DeletionHash.MixedEdit.shared_source_letters n t b k L ⟨hq,ht,hb,hk,hL,hbk,hn⟩ x hx).2 (some e) he
  have hpu : IsUnique m P := by
    rw [← hP]
    exact WindowTools.unique_subwindow hxm a P.length (by rw [hxlen]; omega)
  have hqu : IsUnique m Q := by
    rw [← hQ]
    exact WindowTools.unique_subwindow hym a Q.length (by omega)
  have hpathsP : SpellsSimplePath L P := WindowTools.spells_list L P (by omega) hpu
  have hpathsQ : SpellsSimplePath L Q := WindowTools.spells_list L Q (by omega) hqu
  have hinter : ∀ v, v ∈ PathVertices L P → v ∈ PathVertices L Q →
      List.ofFn v=P.take m ∨ List.ofFn v=P.drop (P.length-m) := by
    intro v hpv hqv
    change List.ofFn v ∈ windows m P at hpv
    change List.ofFn v ∈ windows m Q at hqv
    obtain ⟨i,hi,hepi⟩ := List.mem_map.mp hpv
    obtain ⟨j,hj,heqj⟩ := List.mem_map.mp hqv
    simp only [starts,List.mem_range,if_pos hPm] at hi
    simp only [starts,List.mem_range,if_pos hQm] at hj
    have hip : i+m ≤ P.length := by omega
    have hjq : j+m ≤ Q.length := by omega
    have hepi' : window m (letters x) (a+i)=List.ofFn v := by
      rw [← WindowTools.window_window (letters x) a P.length i m hip,hP,hepi]
    have heqj' : window m y (a+j)=List.ofFn v := by
      rw [← WindowTools.window_window y a Q.length j m hjq,hQ,heqj]
    have h := LocalIntersection.common_windows ⟨hq,ht,hb,hk,hL,hbk,hn⟩ x hx e he hleft hright ends (a+i) (a+j)
      (by change a ≤ a+i ∧ a+i ≤ c; constructor <;> omega)
      (by change a ≤ a+j ∧ a+j ≤ d; constructor <;> omega)
      (hepi'.trans heqj'.symm)
    change (a+i=a ∧ a+j=a) ∨ (a+i=c ∧ a+j=d) at h
    rcases h with h | h
    · rw [h.1] at hepi'
      exact Or.inl (hepi'.symm.trans hfirstP.symm)
    · rw [h.1] at hepi'
      exact Or.inr (hepi'.symm.trans hlastP.symm)
  refine ⟨A,B,X,Y,hframe,hframe',?_,hAlow,hAup,hBlow,hBup,?_,?_⟩
  · omega
  · change Bubble k L b P Q
    refine ⟨⟨A,U,e.replacement,B,rfl,rfl,he.2.2.2,?_,hv,hAlow,hAup,hBlow,hBup⟩,
      hPlow,hPup,hQlow,hQup,hfirst,hlast,hpathsP,hpathsQ,hinter⟩
    omega
  · have h := SpectrumContext.context_cancel X P Q Y m hPm hQm hfirst hlast
    rw [← hword',← hword,← hLm] at h
    exact h

end DeletionGraph.LocalBubble

open DeletionHash.MixedEdit

universe u

/-- Lemma 2.4: actual flanks and unchanged exterior, full path and length geometry. -/
theorem solution {α : Type u} [Fintype α] [DecidableEq α]
    (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (x : Word α n) (hx : IsUnique k (letters x)) (e : Edit α)
    (he : ValidEdit b (letters x) e) (hleft : 2*(L+b) ≤ e.position)
    (hright : e.position+e.removed+2*(L+b) ≤ n) :
    let U := window e.removed (letters x) e.position
    ∃ A B X Y : List α,
      letters x = X ++ A ++ U ++ B ++ Y ∧
      applyEdit e (letters x) = X ++ A ++ e.replacement ++ B ++ Y ∧
      e.position = X.length + A.length ∧
      (L-1)-k-b ≤ A.length ∧ A.length ≤ L-1 ∧
      (L-1)-k-b ≤ B.length ∧ B.length ≤ L-1 ∧
      Bubble k L b (A ++ U ++ B) (A ++ e.replacement ++ B) ∧
      spectrum L (applyEdit e (letters x)) - spectrum L (letters x) =
        spectrum L (A ++ e.replacement ++ B) - spectrum L (A ++ U ++ B) := by exact DeletionGraph.LocalBubble.construct n t b k L hreg x hx e he hleft hright



#print axioms solution
