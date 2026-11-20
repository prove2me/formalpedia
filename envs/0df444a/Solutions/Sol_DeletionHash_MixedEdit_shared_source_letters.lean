-- Prove2me | solution 1 for DeletionHash.MixedEdit.shared_source_letters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:06:57.027786+00:00
-- url     : https://prove2.me/submissions/f4a64d8d-c8f8-47d2-8b92-a21e33540b67

import Mathlib
import Definitions.Def_DeletionHash_MixedEdit_SourceTrace
import Definitions.Def_DeletionHash_MixedEdit_Regime
/- Adapted from Eyal En Gad, deletion-codes-lean, commit 24d093a4 (Apache-2.0). Alphabet generalization preserves the original reconstruction proof. -/
namespace DeletionGeneralization.OverlapCollision
variable (α : Type*) [Fintype α]
abbrev Bits (n : ℕ) := Fin n → α
def padBits {n : ℕ} (x : Bits α n) (i : ℕ) : Option α :=
  if hi : i < n then some (x ⟨i, hi⟩) else none
def Agree (p : ℕ → Option α) (a : ℕ) (q : ℕ → Option α) (b k : ℕ) : Prop :=
  ∀ i, i < k → p (a+i) = q (b+i)
/-- Actual length-n words over an arbitrary finite alphabet whose indicated length-k windows agree. -/
abbrev Collision (n k a b : ℕ) :=
  {x : Bits α n // Agree α (padBits α x) a (padBits α x) b k}

noncomputable instance collisionFintype (n k a b : ℕ) :
    Fintype (Collision α n k a b) := by
  classical
  unfold Collision
  infer_instance

/-- Indices outside the later interval `[b,b+k)`, in their original order. -/
def keptIndex (n k b : ℕ) (hb : b + k ≤ n) (i : Fin (n - k)) : Fin n :=
  if h : i.val < b then ⟨i.val, by omega⟩
  else ⟨i.val + k, by omega⟩

/-- Remove exactly the later substring; retain n-k actual letters. -/
def encode (n k b : ℕ) (hb : b + k ≤ n) (x : Bits α n) : Bits α (n - k) :=
  fun i => x (keptIndex n k b hb i)

/-- Equality of encodings preserves each letter outside the removed interval. -/
theorem encode_eq_at (n k b : ℕ) (hb : b + k ≤ n)
    (x y : Bits α n) (heq : encode α n k b hb x = encode α n k b hb y)
    (j : ℕ) (hj : j < n) (hout : j < b ∨ b + k ≤ j) :
    padBits α x j = padBits α y j := by
  rcases hout with hbefore | hafter
  · have hj' : j < n - k := by omega
    have hh := congrFun heq (⟨j, hj'⟩ : Fin (n - k))
    simpa only [encode, keptIndex, dif_pos hbefore, padBits, dif_pos hj, Option.some.injEq] using hh
  · have hj' : j - k < n - k := by omega
    have hbefore : ¬j - k < b := by omega
    have hrestore : j - k + k = j := by omega
    have hh := congrFun heq (⟨j - k, hj'⟩ : Fin (n - k))
    simpa only [encode, keptIndex, dif_neg hbefore, hrestore,
      padBits, dif_pos hj, Option.some.injEq] using hh

/-- A collision reconstructs each deleted letter from a strictly earlier letter.
No disjointness of the two windows is used. -/
theorem encode_injective_of_agree (n k a b : ℕ) (hab : a < b)
    (hb : b + k ≤ n) (x y : Bits α n)
    (hx : Agree α (padBits α x) a (padBits α x) b k)
    (hy : Agree α (padBits α y) a (padBits α y) b k)
    (heq : encode α n k b hb x = encode α n k b hb y) : x = y := by
  have hall : ∀ j, j < n → padBits α x j = padBits α y j := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj
      by_cases hbefore : j < b
      · exact encode_eq_at α n k b hb x y heq j hj (Or.inl hbefore)
      by_cases hafter : b + k ≤ j
      · exact encode_eq_at α n k b hb x y heq j hj (Or.inr hafter)
      have hoffset : j - b < k := by omega
      have hearlier : a + (j - b) < j := by omega
      have hearlier_bound : a + (j - b) < n := by omega
      have hrestore : b + (j - b) = j := by omega
      have hxcopy := hx (j - b) hoffset
      have hycopy := hy (j - b) hoffset
      rw [hrestore] at hxcopy hycopy
      exact hxcopy.symm.trans ((ih (a + (j - b)) hearlier hearlier_bound).trans hycopy)
  funext j
  simpa only [padBits, dif_pos j.isLt, Option.some.injEq] using hall j.val j.isLt

def collisionEncode (n k a b : ℕ) (hb : b + k ≤ n) :
    Collision α n k a b → Bits α (n - k) :=
  fun x => encode α n k b hb x.val

theorem collisionEncode_injective (n k a b : ℕ) (hab : a < b)
    (hb : b + k ≤ n) : Function.Injective (collisionEncode α n k a b hb) := by
  intro x y heq
  apply Subtype.ext
  exact encode_injective_of_agree α n k a b hab hb x.val y.val x.property y.property heq

/-- The concrete collision set has at most q^(n-k) members, even when the
windows overlap. The earlier window bound follows already from a<b and hb. -/
theorem collision_card_le (n k a b : ℕ) (hab : a < b)
    (_ha : a + k ≤ n) (hb : b + k ≤ n) :
    Fintype.card (Collision α n k a b) ≤ Fintype.card α ^ (n - k) := by
  calc
    Fintype.card (Collision α n k a b) ≤ Fintype.card (Bits α (n - k)) :=
      Fintype.card_le_of_injective (collisionEncode α n k a b hb)
        (collisionEncode_injective α n k a b hab hb)
    _ = Fintype.card α ^ (n - k) := by simp [Bits]

end DeletionGeneralization.OverlapCollision

/-!
A finite union bound over actual pairs of distinct ordered positions a < b.
Their number is derived by an explicit equivalence with a triangular sigma
type; no pair-count or union-cardinality inequality is assumed.
-/
namespace DeletionGeneralization.FinitePairUnion

open scoped BigOperators
open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev OrderedPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- Choose the larger position b, then one of its b smaller positions. -/
def orderedPairEquiv (n : ℕ) : OrderedPair n ≃ Σ b : Fin n, Fin b.val where
  toFun p := ⟨p.val.2, ⟨p.val.1.val, p.property⟩⟩
  invFun p := ⟨(⟨p.2.val, p.2.isLt.trans p.1.isLt⟩, p.1), p.2.isLt⟩
  left_inv := by rintro ⟨⟨a, b⟩, hab⟩; rfl
  right_inv := by rintro ⟨b, a⟩; rfl

/-- The number of pairs a < b among n positions is exactly choose n 2,
including the empty cases n = 0 and n = 1. -/
theorem ordered_pair_card (n : ℕ) : Fintype.card (OrderedPair n) = n.choose 2 := by
  rw [Fintype.card_congr (orderedPairEquiv n), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id, Nat.choose_two_right]

/-- A union of events indexed by a < b has at most choose n 2 times the
maximum event size. The counted set contains each outcome only once. -/
theorem ordered_pair_union_bound {α : Type*} [Fintype α] [DecidableEq α]
    (n M : ℕ) (P : Fin n → Fin n → α → Prop)
    (hcount : ∀ a b, a < b → (univ.filter (P a b)).card ≤ M) :
    (univ.filter (fun x => ∃ a b, a < b ∧ P a b x)).card ≤ n.choose 2 * M := by
  let events : OrderedPair n → Finset α := fun p => univ.filter (P p.val.1 p.val.2)
  have hcover : univ.filter (fun x => ∃ a b, a < b ∧ P a b x) =
      (univ : Finset (OrderedPair n)).biUnion events := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, events]
    constructor
    · rintro ⟨a, b, hab, hx⟩
      exact ⟨⟨(a, b), hab⟩, hx⟩
    · rintro ⟨p, hx⟩
      exact ⟨p.val.1, p.val.2, p.property, hx⟩
  rw [hcover]
  calc
    ((univ : Finset (OrderedPair n)).biUnion events).card ≤
        (univ : Finset (OrderedPair n)).card * M :=
      Finset.card_biUnion_le_card_mul _ events M
        (fun p _ => hcount p.val.1 p.val.2 p.property)
    _ = n.choose 2 * M := by rw [Finset.card_univ, ordered_pair_card]


end

end DeletionGeneralization.FinitePairUnion
namespace DeletionGeneralization.UniqueWordCount
open OverlapCollision
variable (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α]
attribute [local instance] Classical.propDecidable

def KUnique (p : ℕ → Option α) (n k : ℕ) : Prop :=
  ∀ a b, a+k ≤ n → b+k ≤ n → Agree α p a p b k → a=b
noncomputable def uniqueWords (n k : ℕ) : Finset (Bits α n) := by
  classical
  exact Finset.univ.filter (fun x => KUnique α (padBits α x) n k)

noncomputable def nonuniqueWords (n k : ℕ) : Finset (Bits α n) := by
  classical
  exact Finset.univ.filter (fun x => ¬ KUnique α (padBits α x) n k)

/-- Both starting positions are actual valid windows in the finite word. -/
def RepeatedWindow {n : ℕ} (k : ℕ) (a b : Fin n) (x : Bits α n) : Prop :=
  a.val + k ≤ n ∧ b.val + k ≤ n ∧ Agree α (padBits α x) a.val (padBits α x) b.val k

theorem not_unique_iff_pair {n k : ℕ} (hk : 1 ≤ k) (x : Bits α n) :
    ¬ KUnique α (padBits α x) n k ↔
      ∃ a b : Fin n, a < b ∧ RepeatedWindow α k a b x := by
  classical
  constructor
  · intro hx
    simp only [KUnique, not_forall] at hx
    obtain ⟨a, b, ha, hb, hab, hne⟩ := hx
    have han : a < n := by omega
    have hbn : b < n := by omega
    by_cases hlt : a < b
    · exact ⟨⟨a, han⟩, ⟨b, hbn⟩, hlt, ha, hb, hab⟩
    · refine ⟨⟨b, hbn⟩, ⟨a, han⟩, ?_, hb, ha, ?_⟩
      · change b < a
        omega
      · intro i hi
        exact (hab i hi).symm
  · rintro ⟨a, b, hlt, ha, hb, hab⟩ hx
    have heq := hx a.val b.val ha hb hab
    exact (Nat.ne_of_lt hlt) heq

theorem family_partition (n k : ℕ) :
    (uniqueWords α n k).card + (nonuniqueWords α n k).card = Fintype.card α ^ n := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Bits α n))) (fun x => KUnique α (padBits α x) n k)
  simpa only [uniqueWords, nonuniqueWords, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin] using h

theorem unique_of_length_lt {n k : ℕ} (hk : n < k) (x : Bits α n) :
    KUnique α (padBits α x) n k := by
  intro a b ha hb hab
  omega

theorem uniqueWords_eq_univ_of_length_lt {n k : ℕ} (hk : n < k) :
    uniqueWords α n k = Finset.univ := by
  classical
  ext x
  simp only [uniqueWords, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact unique_of_length_lt α hk x

theorem card_uniqueWords_of_length_lt {n k : ℕ} (hk : n < k) :
    (uniqueWords α n k).card = Fintype.card α ^ n := by
  rw [uniqueWords_eq_univ_of_length_lt α hk]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

/-- A fixed pair contributes at most 2^(n-k) words, with overlapping and
out-of-bounds pairs both handled explicitly. -/
theorem repeatedWindow_card_le (n k : ℕ) (a b : Fin n) (hab : a < b) :
    (Finset.univ.filter (RepeatedWindow α k a b)).card ≤ Fintype.card α ^ (n - k) := by
  classical
  by_cases ha : a.val + k ≤ n
  · by_cases hb : b.val + k ≤ n
    · have heq : (Finset.univ.filter (RepeatedWindow α k a b)).card =
          Fintype.card (OverlapCollision.Collision α n k a.val b.val) := by
        rw [Fintype.card_subtype]
        congr 1
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, RepeatedWindow, ha, hb, true_and]
      rw [heq]
      exact OverlapCollision.collision_card_le α n k a.val b.val hab ha hb
    · have hz : Finset.univ.filter (RepeatedWindow α k a b) = ∅ := by
        ext x
        simp [RepeatedWindow, hb]
      rw [hz]
      exact Nat.zero_le _
  · have hz : Finset.univ.filter (RepeatedWindow α k a b) = ∅ := by
      ext x
      simp [RepeatedWindow, ha]
    rw [hz]
    exact Nat.zero_le _

/-- Union bound on the actual nonunique family, counted once per word. -/
theorem nonunique_card_le (n k : ℕ) (hk : 1 ≤ k) :
    (nonuniqueWords α n k).card ≤ n.choose 2 * Fintype.card α ^ (n - k) := by
  classical
  have h := FinitePairUnion.ordered_pair_union_bound n (Fintype.card α ^ (n - k))
    (RepeatedWindow α k) (repeatedWindow_card_le α n k)
  simpa only [nonuniqueWords, not_unique_iff_pair α hk] using h

theorem scaled_nonunique_card_le (n k : ℕ) (hk : 1 ≤ k) :
    (nonuniqueWords α n k).card * Fintype.card α ^ k ≤ n.choose 2 * Fintype.card α ^ n := by
  by_cases hkn : k ≤ n
  · have h := Nat.mul_le_mul_right (Fintype.card α ^ k) (nonunique_card_le α n k hk)
    have hp : Fintype.card α ^ (n - k) * Fintype.card α ^ k = Fintype.card α ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hkn]
    simpa only [Nat.mul_assoc, hp] using h
  · have h := family_partition α n k
    rw [card_uniqueWords_of_length_lt α (by omega)] at h
    have hz : (nonuniqueWords α n k).card = 0 := by omega
    simp only [hz, Nat.zero_mul, Nat.zero_le]

/-- The manuscript's union-bound estimate, with the cardinality of the
actual k-unique family and no assumed collision-probability premise. -/
theorem card_unique_lower_bound (n k : ℕ) (hk : 1 ≤ k) :
    (1 - (n.choose 2 : ℚ) / (Fintype.card α : ℚ) ^ k) * (Fintype.card α : ℚ) ^ n ≤
      (uniqueWords α n k).card := by
  have hpow : (0 : ℚ) < Fintype.card α ^ k := pow_pos (by exact_mod_cast Fintype.card_pos (α := α)) _
  have hscaled : ((nonuniqueWords α n k).card : ℚ) * (Fintype.card α : ℚ) ^ k ≤
      (n.choose 2 : ℚ) * (Fintype.card α : ℚ) ^ n := by
    exact_mod_cast scaled_nonunique_card_le α n k hk
  have hbad : ((nonuniqueWords α n k).card : ℚ) ≤
      (n.choose 2 : ℚ) / (Fintype.card α : ℚ) ^ k * (Fintype.card α : ℚ) ^ n := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hpow).mpr hscaled
  have hpart : ((uniqueWords α n k).card : ℚ) + (nonuniqueWords α n k).card = (Fintype.card α : ℚ) ^ n := by
    exact_mod_cast family_partition α n k
  nlinarith

theorem card_unique_lower_bound_real (n k : ℕ) (hk : 1 ≤ k) :
    (1 - (n.choose 2 : ℝ) / (Fintype.card α : ℝ) ^ k) * (Fintype.card α : ℝ) ^ n ≤
      (uniqueWords α n k).card := by
  have h : (((1 - (n.choose 2 : ℚ) / (Fintype.card α : ℚ) ^ k) * (Fintype.card α : ℚ) ^ n : ℚ) : ℝ) ≤
      (((uniqueWords α n k).card : ℚ) : ℝ) := by
    exact_mod_cast card_unique_lower_bound α n k hk
  simpa only [Rat.cast_mul, Rat.cast_sub, Rat.cast_one, Rat.cast_div,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat] using h

end DeletionGeneralization.UniqueWordCount
namespace DeletionGeneralization.UniqueBridge
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

end DeletionGeneralization.UniqueBridge
namespace DeletionGeneralization.SourceLetters
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

theorem shared [Fintype α] [DecidableEq α] [Nonempty α]
    {n : ℕ} (b k m : ℕ) (hm : 3*k+2*b ≤ m)
    (x : Word α n) (hx : IsUnique k (letters x))
    (e f : Option (Edit α)) (he : ValidOne b (letters x) e) (hf : ValidOne b (letters x) f)
    (i j : ℕ) (hi : i+m ≤ (oneWord (letters x) e).length)
    (hj : j+m ≤ (oneWord (letters x) f).length)
    (heq : window m (oneWord (letters x) e) i = window m (oneWord (letters x) f) j) :
    ∃ o : ℕ, o+k ≤ m ∧ ∀ h : ℕ, h < k → ∃ s : ℕ,
      (sourceTrace (letters x) e)[i+o+h]? = some (some s) ∧
      (sourceTrace (letters x) f)[j+o+h]? = some (some s) := by
  obtain ⟨o, ho, hoe, hof⟩ := common_block m k b i j (cut e) (cut f)
    (newLength e) (newLength f) (newLength_le _ e b he) (newLength_le _ f b hf) hm
  obtain ⟨s, hs, hse⟩ := original_block (letters x) e b (i+o) k he (by omega) (by simpa [Nat.add_assoc] using hoe)
  obtain ⟨v, hv, hvf⟩ := original_block (letters x) f b (j+o) k hf (by omega) (by simpa [Nat.add_assoc] using hof)
  have hs' : s+k ≤ n := by simpa [letters] using hs
  have hv' : v+k ≤ n := by simpa [letters] using hv
  have hsv : s=v := by
    apply (UniqueBridge.unique_iff x).mp hx s v hs' hv'
    intro h hh
    have hh' : o+h < m := by omega
    have hg := congrArg (fun l : List α => l[o+h]?) heq
    have hg' : (oneWord (letters x) e)[i+o+h]? = (oneWord (letters x) f)[j+o+h]? := by
      simpa [window, hh', Nat.add_assoc] using hg
    rw [(hse h hh).1, (hvf h hh).1] at hg'
    simpa [OverlapCollision.padBits, letters, show s+h<n by omega, show v+h<n by omega] using hg'
  subst v
  exact ⟨o, ho, fun h hh => ⟨s+h, (hse h hh).2, (hvf h hh).2⟩⟩

theorem unique_after [Fintype α] [DecidableEq α] [Nonempty α]
    {n : ℕ} (b k m : ℕ) (hk : 0 < k) (hm : 3*k+2*b ≤ m)
    (x : Word α n) (hx : IsUnique k (letters x))
    (e : Option (Edit α)) (he : ValidOne b (letters x) e) :
    IsUnique m (oneWord (letters x) e) := by
  unfold IsUnique windows starts
  rw [List.nodup_map_iff_inj_on List.nodup_range]
  intro i hi j hj hij
  simp only [List.mem_range] at hi hj
  by_cases hfit : m ≤ (oneWord (letters x) e).length
  · simp only [if_pos hfit] at hi hj
    obtain ⟨o, ho, hs⟩ := shared b k m hm x hx e e he he i j (by omega) (by omega) hij
    obtain ⟨s, h1, h2⟩ := hs 0 hk
    have h := trace_injective (letters x) e (i+o+0) (j+o+0) s h1 h2
    omega
  · simp [hfit] at hi



end DeletionGeneralization.SourceLetters
open DeletionHash.MixedEdit

universe u

/-- Lemma 2.3, including the m-uniqueness consequence for every one-edit derivation. -/
theorem solution {α : Type u} [Fintype α] [DecidableEq α]
    (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (x : Word α n) (hx : IsUnique k (letters x)) :
    (∀ e f : Option (Edit α), ValidOne b (letters x) e → ValidOne b (letters x) f →
      ∀ i j : ℕ, i+(L-1) ≤ (oneWord (letters x) e).length →
        j+(L-1) ≤ (oneWord (letters x) f).length →
        window (L-1) (oneWord (letters x) e) i = window (L-1) (oneWord (letters x) f) j →
        ∃ o : ℕ, o+k ≤ L-1 ∧ ∀ h : ℕ, h < k → ∃ s : ℕ,
          (sourceTrace (letters x) e)[i+o+h]? = some (some s) ∧
          (sourceTrace (letters x) f)[j+o+h]? = some (some s)) ∧
    (∀ e : Option (Edit α), ValidOne b (letters x) e → IsUnique (L-1) (oneWord (letters x) e)) := by
  obtain ⟨hq, ht, hb, hk, hL, hbk, hn⟩ := hreg
  letI : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  have hm : 3*k+2*b ≤ L-1 := by omega
  exact ⟨fun e f he hf i j hi hj heq =>
    DeletionGeneralization.SourceLetters.shared b k (L-1) hm x hx e f he hf i j hi hj heq,
    fun e he => DeletionGeneralization.SourceLetters.unique_after b k (L-1)
      (by omega) hm x hx e he⟩



#print axioms solution
