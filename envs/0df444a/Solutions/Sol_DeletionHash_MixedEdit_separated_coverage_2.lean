-- Prove2me | solution 2 for DeletionHash.MixedEdit.separated_coverage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:14:05.169176+00:00
-- url     : https://prove2.me/submissions/e9e33eca-8745-4452-b9c6-394883cd922a

import Definitions.Def_DeletionHash_MixedEdit_Paths
import Definitions.Def_DeletionHash_MixedEdit_Regime
import Definitions.Def_DeletionHash_MixedEdit_Rules
import Definitions.Def_DeletionHash_MixedEdit_SourceTrace
import Definitions.Def_DeletionHash_MixedEdit_UniqueWords
import Mathlib
import Theorems.Thm_DeletionHash_MixedEdit_local_bubble
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
namespace DeletionGraph.RecordWindows
open DeletionHash.MixedEdit SourceLetters WindowTools
universe u
variable {α : Type u}

theorem before (x : List α) (e : Edit α) (he : e.position+e.removed ≤ x.length)
    (i h : ℕ) (hi : i+h ≤ e.position) :
    window h (applyEdit e x) i=window h x i := by
  have hp : e.position ≤ x.length := by omega
  have ht : (applyEdit e x).take e.position=x.take e.position := by
    simp [applyEdit,List.take_append,List.length_take,Nat.min_eq_left hp]
  calc
    _=window h ((applyEdit e x).take e.position) i := (window_take _ _ _ _ hi).symm
    _=window h (x.take e.position) i := by rw [ht]
    _=window h x i := window_take _ _ _ _ hi

theorem after (x : List α) (e : Edit α) (he : e.position+e.removed ≤ x.length)
    (i h : ℕ) (hi : e.position+e.replacement.length ≤ i) :
    window h (applyEdit e x) i=window h x (i-e.replacement.length+e.removed) := by
  have hp : e.position ≤ x.length := by omega
  have hd : (applyEdit e x).drop (e.position+e.replacement.length)=x.drop (e.position+e.removed) := by
    simp [applyEdit,List.drop_append,List.length_take,Nat.min_eq_left hp]
  have heq : i=(e.position+e.replacement.length)+(i-(e.position+e.replacement.length)) := by omega
  unfold window
  conv_lhs => rw [heq,←List.drop_drop,hd,List.drop_drop]
  congr 2
  omega

theorem pullback_single (b : ℕ) (x : List α) (e : Edit α) (he : ValidEdit b x e)
    (i h : ℕ) (hi : i+h ≤ (applyEdit e x).length)
    (hfar : i+h ≤ e.position ∨ e.position+e.replacement.length ≤ i) :
    ∃ a, a+h ≤ x.length ∧ window h (applyEdit e x) i=window h x a ∧
      a ≤ i+b ∧ i ≤ a+b := by
  have hn := edited_length x e he.1
  rcases hfar with hf | hf
  · exact ⟨i,by have hh:=he.1;omega,before x e he.1 i h hf,by omega,by omega⟩
  · refine ⟨i-e.replacement.length+e.removed,?_,after x e he.1 i h hf,?_,?_⟩
    all_goals have hu:=he.2.1;have hv:=he.2.2.1;have hh:=he.1;omega

theorem pullback (b : ℕ) (x : List α) (record : List (Edit α))
    (hr : ValidRecord b x record) (i h : ℕ) (hi : i+h ≤ (target x record).length)
    (hfar : ∀ e ∈ record,
      i+h+record.length*b ≤ e.position ∨ e.position+(record.length+1)*b ≤ i) :
    ∃ a, a+h ≤ x.length ∧ window h (target x record) i=window h x a ∧
      a ≤ i+record.length*b ∧ i ≤ a+record.length*b := by
  induction record generalizing x with
  | nil => exact ⟨i,hi,rfl,by simp,by simp⟩
  | cons e es ih =>
    have hlen : (e::es).length=es.length+1 := rfl
    have hrest : ∀ f ∈ es, i+h+es.length*b ≤ f.position ∨ f.position+(es.length+1)*b ≤ i := by
      intro f hf
      have hd := hfar f (List.mem_cons_of_mem _ hf)
      rw [hlen] at hd
      rcases hd with hd | hd
      · left; nlinarith
      · right; nlinarith
    obtain ⟨a,ha,heq,ha1,ha2⟩ := ih (applyEdit e x) hr.2 hi hrest
    have hef : a+h ≤ e.position ∨ e.position+e.replacement.length ≤ a := by
      have hd := hfar e (List.mem_cons_self)
      rw [hlen] at hd
      have hb := hr.1.2.2.1
      rcases hd with hd | hd
      · left; nlinarith
      · right; nlinarith
    obtain ⟨c,hc,hec,hc1,hc2⟩ := pullback_single b x e hr.1 a h ha hef
    refine ⟨c,hc,heq.trans hec,?_,?_⟩
    · rw [hlen]; nlinarith
    · rw [hlen]; nlinarith

end DeletionGraph.RecordWindows
namespace DeletionGraph.RecordStates
open DeletionHash.MixedEdit SourceLetters
universe u
variable {α : Type u}

theorem valid_take (b : ℕ) (x : List α) (r : List (Edit α))
    (hv : ValidRecord b x r) (j : ℕ) : ValidRecord b x (r.take j) := by
  induction r generalizing x j with
  | nil => simp [ValidRecord]
  | cons e r ih =>
    cases j with
    | zero => trivial
    | succ j => exact ⟨hv.1,ih (applyEdit e x) hv.2 j⟩

theorem valid_step (b : ℕ) (x : List α) (r : List (Edit α))
    (hv : ValidRecord b x r) (j : Fin r.length) :
    ValidEdit b (target x (r.take j.val)) (r.get j) := by
  induction r generalizing x with
  | nil => exact Fin.elim0 j
  | cons e r ih =>
    cases j using Fin.cases with
    | zero => exact hv.1
    | succ j => exact ih (applyEdit e x) hv.2 j

theorem length_bounds (b : ℕ) (x : List α) (r : List (Edit α))
    (hv : ValidRecord b x r) :
    (target x r).length ≤ x.length+r.length*b ∧
      x.length ≤ (target x r).length+r.length*b := by
  induction r generalizing x with
  | nil => simp [target]
  | cons e r ih =>
    obtain ⟨h1,h2⟩ := ih (applyEdit e x) hv.2
    have hlen := edited_length x e hv.1.1
    have hu := hv.1.2.1
    have hvv := hv.1.2.2.1
    have hp := hv.1.1
    change (target (applyEdit e x) r).length ≤ x.length+(r.length+1)*b ∧
      x.length ≤ (target (applyEdit e x) r).length+(r.length+1)*b
    constructor <;> nlinarith [Nat.sub_add_cancel hp]

theorem prior_index (r : List (Edit α)) (j : Fin r.length)
    (e : Edit α) (he : e ∈ r.take j.val) :
    ∃ i : Fin r.length, i.val<j.val ∧ r.get i=e := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp he
  have hib := i.isLt
  simp only [List.length_take] at hib
  have hij : i.val<j.val := by omega
  have hir : i.val<r.length := by omega
  refine ⟨⟨i.val,hir⟩,hij,?_⟩
  simpa only [List.get_eq_getElem,List.getElem_take] using hi

end DeletionGraph.RecordStates
namespace DeletionGraph.SeparatedWindows
open DeletionHash.MixedEdit RecordStates WindowTools
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem source_window (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (x : Word α n) (hx : IsUnique k (letters x)) (r : List (Edit α))
    (hv : ValidRecord b (letters x) r) (hlen : r.length=2*t)
    (hsep : Separated n t b L r) (j : Fin r.length) :
    let p := (r.get j).position
    let M := 2*(L+b)
    let W := window (2*M+b) (target (letters x) (r.take j.val)) (p-M)
    ∃ a, a+(2*M+b) ≤ n ∧ W=window (2*M+b) (letters x) a ∧
      a ≤ p-M+j.val*b ∧ p-M ≤ a+j.val*b ∧ IsUnique k W ∧ W.length=2*M+b := by
  dsimp
  let p := (r.get j).position
  let M := 2*(L+b)
  let s := r.take j.val
  have ht : 2 ≤ t := hreg.2.1
  have hb : 1 ≤ b := hreg.2.2.1
  have hL : L=3*(k+b+1) := hreg.2.2.2.2.1
  have hj : j.val < 2*t := by simpa only [hlen] using j.isLt
  have hjs : s.length=j.val := by
    dsimp [s]
    rw [List.length_take,Nat.min_eq_left (Nat.le_of_lt j.isLt)]
  have hvalid : ValidRecord b (letters x) s := valid_take b (letters x) r hv j.val
  have hmargin := hsep.1 (r.get j) (List.get_mem _ _)
  change 8*(L+t*b) ≤ p ∧ p+8*(L+t*b) ≤ n at hmargin
  have hbudget : M+(j.val+1)*b ≤ 8*(L+t*b) := by
    dsimp [M]
    have hmul := Nat.mul_le_mul_right b (show j.val+1 ≤ 2*t by omega)
    nlinarith
  have hpM : M ≤ p := by nlinarith [hmargin.1]
  have hxy := length_bounds b (letters x) s hvalid
  have hxlen : (letters x).length=n := by simp [letters]
  rw [hjs,hxlen] at hxy
  have hwin : p-M+(2*M+b) ≤ (target (letters x) s).length := by
    nlinarith [hmargin.2,Nat.sub_add_cancel hpM]
  have hfar : ∀ e ∈ s,
      p-M+(2*M+b)+s.length*b ≤ e.position ∨ e.position+(s.length+1)*b ≤ p-M := by
    intro e he
    obtain ⟨i,hij,hie⟩ := prior_index r j e he
    have hne : i ≠ j := by intro h; subst i; omega
    have hd := hsep.2 i j hne
    rw [hie] at hd
    change 8*(L+t*b) ≤ Nat.dist e.position p at hd
    rw [hjs]
    rcases Nat.le_total e.position p with hep | hpe
    · right
      rw [Nat.dist_eq_sub_of_le hep] at hd
      have hgap : e.position+8*(L+t*b) ≤ p := by omega
      nlinarith [Nat.sub_add_cancel hpM]
    · left
      rw [Nat.dist_eq_sub_of_le_right hpe] at hd
      have hgap : p+8*(L+t*b) ≤ e.position := by omega
      nlinarith [Nat.sub_add_cancel hpM]
  obtain ⟨a,ha,he,ha1,ha2⟩ := RecordWindows.pullback b (letters x) s hvalid
    (p-M) (2*M+b) hwin hfar
  rw [hxlen] at ha
  rw [hjs] at ha1 ha2
  have hu : IsUnique k (window (2*M+b) (target (letters x) s) (p-M)) := by
    rw [he]
    exact unique_subwindow hx a (2*M+b) (by rwa [hxlen])
  have hwlen : (window (2*M+b) (target (letters x) s) (p-M)).length=2*M+b := by
    simp only [window,List.length_take,List.length_drop]
    omega
  exact ⟨a,ha,he,ha1,ha2,hu,hwlen⟩

end DeletionGraph.SeparatedWindows
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
namespace DeletionGraph.LocalContext
open DeletionHash.MixedEdit WindowTools
universe u
variable {α : Type u}

theorem apply_context (X W Y : List α) (e : Edit α)
    (he : e.position+e.removed ≤ W.length) :
    applyEdit ⟨X.length+e.position,e.removed,e.replacement⟩ (X++W++Y) =
      X++applyEdit e W++Y := by
  have hp : e.position ≤ W.length := by omega
  simp [applyEdit,List.take_append,List.drop_append,List.append_assoc,
    Nat.min_eq_left hp,Nat.min_eq_left he,Nat.add_assoc,
    List.take_of_length_le (show X.length ≤ X.length+e.position by omega),
    List.drop_eq_nil_of_le (show X.length ≤ X.length+(e.position+e.removed) by omega),
    Nat.sub_eq_zero_of_le hp,Nat.sub_eq_zero_of_le he]

theorem window_context (X W Y : List α) (i h : ℕ) (hi : i+h ≤ W.length) :
    window h (X++W++Y) (X.length+i)=window h W i := by
  have hp : i ≤ W.length := by omega
  simp [window,List.drop_append,List.take_append,List.append_assoc,
    Nat.min_eq_left hp,Nat.min_eq_left (show h ≤ W.length-i by omega),
    List.drop_eq_nil_of_le (show X.length ≤ X.length+i by omega),
    Nat.sub_eq_zero_of_le (show h ≤ W.length-i by omega)]

theorem valid_context [DecidableEq α] (b : ℕ) (X W Y : List α) (e : Edit α)
    (he : ValidEdit b W e) :
    ValidEdit b (X++W++Y) ⟨X.length+e.position,e.removed,e.replacement⟩ := by
  refine ⟨?_,he.2.1,he.2.2.1,?_⟩
  · simp only [List.length_append]
    have h:=he.1
    omega
  · change window e.removed (X++W++Y) (X.length+e.position) ≠ e.replacement
    rw [window_context X W Y e.position e.removed he.1]
    exact he.2.2.2

theorem slice_frame (a H : ℕ) (X P Y : List α)
    (ha : a ≤ X.length) (hfit : X.length-a+P.length ≤ H) :
    window H (X++P++Y) a =
      X.drop a ++ P ++ Y.take (H-(X.length-a+P.length)) := by
  have hx : (X.drop a).length ≤ H := by simp only [List.length_drop]; omega
  have hp : P.length ≤ H-(X.length-a) := by omega
  simp only [List.append_assoc, window, List.drop_append, Nat.sub_eq_zero_of_le ha,
    List.drop_zero, List.take_append, List.take_of_length_le hx,
    List.take_of_length_le hp, List.length_drop, Nat.sub_sub, Nat.zero_sub]

theorem construct [Fintype α] [DecidableEq α]
    (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (x : Word α n) (hx : IsUnique k (letters x))
    (a0 H : ℕ) (W : List α) (hWsrc : W=window H (letters x) a0)
    (hWlen : W.length=H) (ha0 : a0+H ≤ n)
    (e : Edit α) (he : ValidEdit b W e) (hl : 2*(L+b) ≤ e.position)
    (hr : e.position+e.removed+2*(L+b) ≤ W.length) :
    ∃ A B X Y : List α,
      W=X++A++window e.removed W e.position++B++Y ∧
      applyEdit e W=X++A++e.replacement++B++Y ∧
      e.position=X.length+A.length ∧ A.length ≤ L-1 ∧ B.length ≤ L-1 ∧
      Bubble k L b (A++window e.removed W e.position++B) (A++e.replacement++B) := by
  let XS := (letters x).take a0
  let YS := (letters x).drop (a0+H)
  have hXS : XS.length=a0 := by
    simp only [XS,List.length_take,letters,List.length_ofFn]
    omega
  have hsource : letters x=XS++W++YS := by
    rw [hWsrc]
    simp only [XS,YS,window,List.append_assoc,←List.drop_drop,List.take_append_drop]
  let f : Edit α := ⟨a0+e.position,e.removed,e.replacement⟩
  have hf : ValidEdit b (letters x) f := by
    rw [hsource]
    simpa only [hXS,f] using valid_context b XS W YS e he
  have hfleft : 2*(L+b) ≤ f.position := by dsimp [f];omega
  have hfright : f.position+f.removed+2*(L+b) ≤ n := by dsimp [f];omega
  obtain ⟨A,B,Xg,Yg,hframe,_,hpos,_,hA,_,hB,hbubble,_⟩ :=
    DeletionHash.MixedEdit.local_bubble n t b k L hreg x hx f hf hfleft hfright
  have hUeq : window f.removed (letters x) f.position=window e.removed W e.position := by
    rw [hsource]
    simpa only [f,←hXS] using window_context XS W YS e.position e.removed he.1
  rw [hUeq] at hframe hbubble
  change a0+e.position=Xg.length+A.length at hpos
  have hUlen : (window e.removed W e.position).length=e.removed := by
    simp only [window,List.length_take,List.length_drop]
    have hh:=he.1
    omega
  let P := A++window e.removed W e.position++B
  have hword : letters x=Xg++P++Yg := by simpa only [P,List.append_assoc] using hframe
  have haX : a0 ≤ Xg.length := by omega
  have hfit : Xg.length-a0+P.length ≤ H := by
    simp only [P,List.length_append,hUlen]
    omega
  let X := Xg.drop a0
  let Y := Yg.take (H-(Xg.length-a0+P.length))
  have hlocal : W=X++A++window e.removed W e.position++B++Y := by
    have h := slice_frame a0 H Xg P Yg haX hfit
    rw [←hword,←hWsrc] at h
    simpa only [X,Y,P,List.append_assoc] using h
  have hlocalpos : e.position=X.length+A.length := by
    simp only [X,List.length_drop]
    omega
  refine ⟨A,B,X,Y,hlocal,?_,hlocalpos,hA,hB,hbubble⟩
  let U := window e.removed W e.position
  have heq : e=⟨(X++A).length+0,U.length,e.replacement⟩ := by
    cases e
    simp only [Edit.mk.injEq,List.length_append,Nat.add_zero]
    exact ⟨hlocalpos,hUlen.symm,True.intro⟩
  have h := apply_context (X++A) U (B++Y) ⟨0,U.length,e.replacement⟩ (by simp)
  calc
    applyEdit e W = applyEdit ⟨(X++A).length+0,U.length,e.replacement⟩ ((X++A)++U++(B++Y)) := by
      conv_lhs => rw [hlocal]
      rw [←heq]
      simp only [U,List.append_assoc]
    _ = (X++A)++applyEdit ⟨0,U.length,e.replacement⟩ U++(B++Y) := h
    _ = X++A++e.replacement++B++Y := by simp [applyEdit,List.append_assoc]

end DeletionGraph.LocalContext
namespace DeletionGraph.SeparatedBubble
open DeletionHash.MixedEdit WindowTools RecordStates
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem window_frame (x : List α) (i h : ℕ) :
    x=x.take i++window h x i++x.drop (i+h) := by
  simp only [window,List.append_assoc,←List.drop_drop,List.take_append_drop]

theorem step (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (x : Word α n) (hx : IsUnique k (letters x)) (r : List (Edit α))
    (hv : ValidRecord b (letters x) r) (hlen : r.length=2*t)
    (hsep : Separated n t b L r) (j : Fin r.length) :
    let y := target (letters x) (r.take j.val)
    let e := r.get j
    ∃ (f : Edit α) (P Q : List α) (a : ℕ),
      ValidEdit b (letters x) f ∧ Bubble k L b P Q ∧
      spectrum L (applyEdit e y)-spectrum L y=spectrum L Q-spectrum L P ∧
      window P.length (letters x) a=P ∧
      window Q.length (applyEdit f (letters x)) a=Q ∧
      a+P.length ≤ n ∧ a+Q.length ≤ (applyEdit f (letters x)).length ∧
      a ≤ f.position ∧ f.position ≤ a+(L-1) ∧
      a+P.length ≤ f.position+b+(L-1) ∧ a+Q.length ≤ f.position+b+(L-1) ∧
      f.position ≤ e.position+j.val*b ∧ e.position ≤ f.position+j.val*b := by
  dsimp only
  let e := r.get j
  let y := target (letters x) (r.take j.val)
  let M := 2*(L+b)
  let H := 2*M+b
  let i := e.position-M
  let W := window H y i
  have he : ValidEdit b y e := valid_step b (letters x) r hv j
  have hp0 := hsep.1 (r.get j) (List.get_mem _ _)
  have ht := hreg.2.1
  have hLg := hreg.2.2.2.2.1
  have hp : M ≤ e.position := by
    change 2*(L+b) ≤ (r.get j).position
    nlinarith [hp0.1]
  have hi : i+M=e.position := by dsimp [i];omega
  obtain ⟨a0,ha0,hWsrc,ha1,ha2,hWu,hWlen⟩ := SeparatedWindows.source_window n t b k L hreg x hx r hv hlen hsep j
  change a0+H ≤ n at ha0
  change W=window H (letters x) a0 at hWsrc
  change a0 ≤ i+j.val*b at ha1
  change i ≤ a0+j.val*b at ha2
  change IsUnique k W at hWu
  change W.length=H at hWlen
  let e0 : Edit α := ⟨M,e.removed,e.replacement⟩
  have hu := he.2.1
  have he0 : ValidEdit b W e0 := by
    refine ⟨?_,he.2.1,he.2.2.1,?_⟩
    · change M+e.removed ≤ W.length
      rw [hWlen]
      dsimp [H]
      omega
    · change window e.removed W M ≠ e.replacement
      have h := window_window y i H M e.removed (by dsimp [H];omega)
      change window e.removed W M=window e.removed y (i+M) at h
      rw [h,hi]
      exact he.2.2.2
  obtain ⟨A,B,X,Y,hframe,hframe',hpos,hA,hB,hbubble⟩ := LocalContext.construct n t b k L hreg x hx a0 H W hWsrc hWlen ha0 e0 he0 (by rfl)
      (by change M+e.removed+M ≤ W.length;rw [hWlen];dsimp [H];omega)
  let U := window e.removed W M
  let P := A++U++B
  let Q := A++e.replacement++B
  have hP : W=X++P++Y := by simpa only [P,U,e0,List.append_assoc] using hframe
  have hQ : applyEdit e0 W=X++Q++Y := by simpa only [Q,e0,List.append_assoc] using hframe'
  have hbubble : Bubble k L b P Q := hbubble
  have hU : U.length=e.removed := by
    dsimp [U,window]
    simp only [List.length_take,List.length_drop,hWlen]
    dsimp [H]
    omega
  have hpos : M=X.length+A.length := hpos
  let XS := (letters x).take a0
  let YS := (letters x).drop (a0+H)
  have hXS : XS.length=a0 := by
    dsimp [XS]
    simp only [List.length_take]
    have hxlen : (letters x).length=n := by simp [letters]
    rw [hxlen];omega
  have hsource : letters x=XS++W++YS := by
    rw [hWsrc]
    exact window_frame _ a0 H
  let f : Edit α := ⟨a0+M,e.removed,e.replacement⟩
  have hf : ValidEdit b (letters x) f := by
    rw [hsource]
    simpa only [hXS,e0,f] using LocalContext.valid_context b XS W YS e0 he0
  have hsource' : applyEdit f (letters x)=XS++applyEdit e0 W++YS := by
    rw [hsource]
    simpa only [hXS,e0,f] using LocalContext.apply_context XS W YS e0 he0.1
  have hsourceP : letters x=(XS++X)++P++(Y++YS) := by
    rw [hsource,hP];simp only [List.append_assoc]
  have hsourceQ : applyEdit f (letters x)=(XS++X)++Q++(Y++YS) := by
    rw [hsource',hQ];simp only [List.append_assoc]
  have hylen : i+H ≤ y.length := by
    have h := hWlen
    dsimp [W,window] at h
    simp only [List.length_take,List.length_drop] at h
    dsimp [H,M] at h ⊢
    omega
  let XC := y.take i
  let YC := y.drop (i+H)
  have hXC : XC.length=i := by
    dsimp [XC];simp only [List.length_take];omega
  have hcurrent : y=XC++W++YC := window_frame y i H
  have hcurrent' : applyEdit e y=XC++applyEdit e0 W++YC := by
    rw [hcurrent]
    have heq : e=⟨XC.length+e0.position,e0.removed,e0.replacement⟩ := by
      have h : e.position=XC.length+e0.position := by simpa only [hXC,e0] using hi.symm
      calc
        e=⟨e.position,e.removed,e.replacement⟩ := rfl
        _=⟨XC.length+e0.position,e0.removed,e0.replacement⟩ := by rw [h]
    rw [heq]
    exact LocalContext.apply_context XC W YC e0 he0.1
  have hcurrentP : y=(XC++X)++P++(Y++YC) := by
    rw [hcurrent,hP];simp only [List.append_assoc]
  have hcurrentQ : applyEdit e y=(XC++X)++Q++(Y++YC) := by
    rw [hcurrent',hQ];simp only [List.append_assoc]
  have hspectrum : spectrum L (applyEdit e y)-spectrum L y=spectrum L Q-spectrum L P := by
    have hL1 : 1 ≤ L := by omega
    have h := SpectrumContext.context_cancel (XC++X) P Q (Y++YC) (L-1)
      (by have h:=hbubble.2.1;omega) (by have h:=hbubble.2.2.2.1;omega)
      hbubble.2.2.2.2.2.1 hbubble.2.2.2.2.2.2.1
    have hLe : L-1+1=L := by omega
    rw [hLe,←hcurrentP,←hcurrentQ] at h
    exact h
  refine ⟨f,P,Q,a0+X.length,hf,hbubble,hspectrum,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hsourceP]
    simpa only [List.length_append,hXS] using window_of_append (XS++X) P (Y++YS)
  · rw [hsourceQ]
    simpa only [List.length_append,hXS] using window_of_append (XS++X) Q (Y++YS)
  · have h := congrArg List.length hsourceP
    simp only [List.length_append,hXS,letters,List.length_ofFn] at h
    omega
  · have h := congrArg List.length hsourceQ
    simp only [List.length_append,hXS] at h
    omega
  · dsimp [f];omega
  · dsimp [f];omega
  · dsimp [f,P]
    simp only [List.length_append,hU]
    omega
  · dsimp [f,Q]
    simp only [List.length_append]
    have hvv := he.2.2.1
    omega
  · change a0+M ≤ e.position+j.val*b
    omega
  · change e.position ≤ a0+M+j.val*b
    omega

end DeletionGraph.SeparatedBubble
namespace DeletionGraph.SeparatedDisjoint
open DeletionHash.MixedEdit SourceLetters WindowTools
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem trace_shift (b : ℕ) (x : List α) (e : Option (Edit α))
    (he : ValidOne b x e) (i s : ℕ)
    (h : (sourceTrace x e)[i]?=some (some s)) : s ≤ i+b ∧ i ≤ s+b := by
  cases e with
  | none =>
    by_cases hi : i<x.length
    · have hs : i=s := by simpa [sourceTrace,hi] using h
      omega
    · simp [sourceTrace,hi] at h
  | some e =>
    obtain hf | hf := trace_position x e i s h
    · omega
    · have hu := he.2.1
      have hv := he.2.2.1
      omega

theorem positions_close [Nonempty α] {n : ℕ} (b k m : ℕ) (hk : 0<k)
    (hm : 3*k+2*b ≤ m) (t L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (hmL : m=L-1) (x : Word α n) (hx : IsUnique k (letters x))
    (e f : Option (Edit α)) (he : ValidOne b (letters x) e) (hf : ValidOne b (letters x) f)
    (p q i j : ℕ) (hi : i+m ≤ (oneWord (letters x) e).length)
    (hj : j+m ≤ (oneWord (letters x) f).length)
    (hpi : p ≤ i+m) (hip : i ≤ p+b) (hqj : q ≤ j+m) (hjq : j ≤ q+b)
    (hw : window m (oneWord (letters x) e) i=window m (oneWord (letters x) f) j) :
    p ≤ q+2*m+3*b ∧ q ≤ p+2*m+3*b := by
  subst m
  obtain ⟨o,ho,hs⟩ := (DeletionHash.MixedEdit.shared_source_letters n t b k L hreg x hx).1 e f he hf i j hi hj hw
  obtain ⟨s,hs1,hs2⟩ := hs 0 hk
  simp only [Nat.add_zero] at hs1 hs2
  have h1 := trace_shift b (letters x) e he (i+o) s hs1
  have h2 := trace_shift b (letters x) f hf (j+o) s hs2
  constructor <;> omega

theorem vertex_window {n b k L : ℕ} (x : Word α n) (f : Edit α)
    (hf : ValidEdit b (letters x) f) (P Q : List α) (a : ℕ)
    (hB : Bubble k L b P Q) (hL : 1 ≤ L)
    (hP : window P.length (letters x) a=P)
    (hQ : window Q.length (applyEdit f (letters x)) a=Q)
    (hnP : a+P.length ≤ n) (hnQ : a+Q.length ≤ (applyEdit f (letters x)).length)
    (hpa : f.position ≤ a+(L-1))
    (hpP : a+P.length ≤ f.position+b+(L-1))
    (hpQ : a+Q.length ≤ f.position+b+(L-1))
    (v : Gram α (L-1)) (hv : v ∈ bubbleVertices L P Q) :
    ∃ (e : Option (Edit α)) (i : ℕ), ValidOne b (letters x) e ∧
      i+(L-1) ≤ (oneWord (letters x) e).length ∧
      window (L-1) (oneWord (letters x) e) i=List.ofFn v ∧
      f.position ≤ i+(L-1) ∧ i ≤ f.position+b := by
  have hmP : L-1 ≤ P.length := by have h:=hB.2.1;omega
  have hmQ : L-1 ≤ Q.length := by have h:=hB.2.2.2.1;omega
  rcases hv with hv | hv
  · change List.ofFn v ∈ windows (L-1) P at hv
    obtain ⟨i,hi,he⟩ := List.mem_map.mp hv
    simp only [starts,List.mem_range,if_pos hmP] at hi
    have hip : i+(L-1) ≤ P.length := by omega
    refine ⟨none,a+i,by trivial,?_,?_,by omega,by omega⟩
    · simp only [oneWord,letters,List.length_ofFn];omega
    · change window (L-1) (letters x) (a+i)=List.ofFn v
      rw [←window_window _ a P.length i (L-1) hip,hP,he]
  · change List.ofFn v ∈ windows (L-1) Q at hv
    obtain ⟨i,hi,he⟩ := List.mem_map.mp hv
    simp only [starts,List.mem_range,if_pos hmQ] at hi
    have hiq : i+(L-1) ≤ Q.length := by omega
    refine ⟨some f,a+i,hf,?_,?_,by omega,by omega⟩
    · change a+i+(L-1) ≤ (applyEdit f (letters x)).length
      omega
    · change window (L-1) (applyEdit f (letters x)) (a+i)=List.ofFn v
      rw [←window_window _ a Q.length i (L-1) hiq,hQ,he]

end DeletionGraph.SeparatedDisjoint
namespace DeletionGraph.SeparatedCoverage
open DeletionHash.MixedEdit SeparatedDisjoint
universe u v
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem telescope {A : Type v} [AddCommGroup A] (F : List α → A)
    (x : List α) (r : List (Edit α)) :
    F (target x r)-F x =
      ∑ j : Fin r.length,
        (F (applyEdit (r.get j) (target x (r.take j.val)))-F (target x (r.take j.val))) := by
  induction r generalizing x with
  | nil => simp [target]
  | cons e es ih =>
    change F (target x (e::es))-F x = ∑ j : Fin (es.length+1),
      (F (applyEdit ((e::es).get j) (target x ((e::es).take j.val)))-F (target x ((e::es).take j.val)))
    rw [Fin.sum_univ_succ]
    change F (target (applyEdit e x) es)-F x =
      (F (applyEdit e x)-F x)+
        ∑ j : Fin es.length,
          (F (applyEdit (es.get j) (target (applyEdit e x) (es.take j.val)))-
            F (target (applyEdit e x) (es.take j.val)))
    rw [←ih (applyEdit e x)]
    abel

theorem coverage (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (x : Word α n) (hx : IsUnique k (letters x)) (r : List (Edit α))
    (hv : ValidRecord b (letters x) r) (hlen : r.length=2*t)
    (hsep : Separated n t b L r) :
    spectrum L (target (letters x) r)-spectrum L (letters x) ∈ Catalogue k L t b := by
  classical
  letI : Nonempty α := Fintype.card_pos_iff.mp (by have h:=hreg.1;omega)
  choose f P Q a hf hB hs hP hQ hnP hnQ ha hpa hpP hpQ hfp hpf using
    fun j => SeparatedBubble.step n t b k L hreg x hx r hv hlen hsep j
  have hLg : L=3*(k+b+1) := hreg.2.2.2.2.1
  have ht : 2 ≤ t := hreg.2.1
  have hb : 1 ≤ b := hreg.2.2.1
  have hbk : b<k := hreg.2.2.2.2.2.1
  have hL : 1 ≤ L := by omega
  have hdis : ∀ i j : Fin r.length, i ≠ j →
      Disjoint (bubbleVertices L (P i) (Q i)) (bubbleVertices L (P j) (Q j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro v hvi hvj
    obtain ⟨e,pi,he,hip,hwi,hpi,hpi'⟩ := vertex_window x (f i) (hf i)
      (P i) (Q i) (a i) (hB i) hL (hP i) (hQ i) (hnP i) (hnQ i)
      (hpa i) (hpP i) (hpQ i) v hvi
    obtain ⟨e',pj,he',hjp,hwj,hpj,hpj'⟩ := vertex_window x (f j) (hf j)
      (P j) (Q j) (a j) (hB j) hL (hP j) (hQ j) (hnP j) (hnQ j)
      (hpa j) (hpP j) (hpQ j) v hvj
    have hc := positions_close b k (L-1) (by omega) (by omega) t L hreg rfl x hx e e' he he'
      (f i).position (f j).position pi pj hip hjp hpi hpi' hpj hpj'
      (hwi.trans hwj.symm)
    have hd := hsep.2 i j hij
    have hi : i.val ≤ 2*t := by have h:=i.isLt;omega
    have hj : j.val ≤ 2*t := by have h:=j.isLt;omega
    have hib := Nat.mul_le_mul_right b hi
    have hjb := Nat.mul_le_mul_right b hj
    have hfi := hfp i
    have hfj := hfp j
    have hif := hpf i
    have hjf := hpf j
    rcases Nat.le_total (r.get i).position (r.get j).position with hpij | hpji
    · rw [Nat.dist_eq_sub_of_le hpij] at hd
      have hgap : (r.get i).position+8*(L+t*b) ≤ (r.get j).position := by omega
      nlinarith [Nat.sub_le L 1]
    · rw [Nat.dist_eq_sub_of_le_right hpji] at hd
      have hgap : (r.get j).position+8*(L+t*b) ≤ (r.get i).position := by omega
      nlinarith [Nat.sub_le L 1]
  let E : Fin (2*t) ≃ Fin r.length := finCongr hlen.symm
  refine ⟨fun i => (P (E i),Q (E i)),fun i => hB (E i),
    fun i j hij => hdis (E i) (E j) (fun he => hij (E.injective he)),?_⟩
  have hsum := telescope (spectrum L) (letters x) r
  simp_rw [hs] at hsum
  calc
    _ = ∑ j : Fin r.length, (spectrum L (Q j)-spectrum L (P j)) := hsum
    _ = ∑ i : Fin (2*t), (spectrum L (Q (E i))-spectrum L (P (E i))) :=
      (E.sum_comp (fun j => spectrum L (Q j)-spectrum L (P j))).symm

end DeletionGraph.SeparatedCoverage
open DeletionHash.MixedEdit

universe u

/-- Lemma 2.7: exactly 2t separated edits, returning to the original length. -/
theorem solution {α : Type u} [Fintype α] [DecidableEq α]
    (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (x : Word α n) (hx : IsUnique k (letters x)) (record : List (Edit α))
    (hvalid : ValidRecord b (letters x) record) (hlen : record.length = 2*t)
    (hsep : Separated n t b L record) (htarget : (target (letters x) record).length = n) :
    spectrum L (target (letters x) record) - spectrum L (letters x) ∈ Catalogue k L t b := by exact DeletionGraph.SeparatedCoverage.coverage n t b k L hreg x hx record hvalid hlen hsep



#print axioms solution
