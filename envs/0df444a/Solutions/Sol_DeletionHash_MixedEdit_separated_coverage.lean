-- Prove2me | solution 1 for DeletionHash.MixedEdit.separated_coverage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:13:29.87723+00:00
-- url     : https://prove2.me/submissions/645816ea-7a88-424f-a9d9-49b92a3d559b

import Definitions.Def_DeletionHash_MixedEdit_Bubbles
import Definitions.Def_DeletionHash_MixedEdit_Edits
import Definitions.Def_DeletionHash_MixedEdit_Paths
import Definitions.Def_DeletionHash_MixedEdit_Regime
import Definitions.Def_DeletionHash_MixedEdit_Rules
import Definitions.Def_DeletionHash_MixedEdit_SourceTrace
import Definitions.Def_DeletionHash_MixedEdit_UniqueWords
import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Basic
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
namespace DeletionGeneralization.WordPaths
open OverlapCollision UniqueWordCount
variable (α : Type*)
/-- A length-L window has a valid occurrence in the finite prefix of x. -/
def Occurs (x : (ℕ → Option α)) (n : ℕ) (p : (ℕ → Option α)) (i L : ℕ) : Prop :=
  ∃ a, a + L ≤ n ∧ Agree α x a p i L

/-- Two consecutive L-windows must occur consecutively in a k-unique x. -/
theorem consecutive_occurrences
    (x p : (ℕ → Option α)) (n k L i a b : ℕ)
    (hx : KUnique α x n k) (hk : k < L)
    (ha : a + L ≤ n) (hb : b + L ≤ n)
    (hleft : Agree α x a p i L) (hright : Agree α x b p (i + 1) L) :
    b = a + 1 := by
  have hmatch : Agree α x (a + 1) x b k := by
    intro j hj
    have hl := hleft (j + 1) (by omega)
    have hr := hright j (by omega)
    calc
      x (a + 1 + j) = x (a + (j + 1)) := congrArg x (by omega)
      _ = p (i + (j + 1)) := hl
      _ = p (i + 1 + j) := congrArg p (by omega)
      _ = x (b + j) := hr.symm
  exact (hx (a + 1) b (by omega) (by omega) hmatch).symm

/--
All L-windows of p occurring in x forces the whole length-(L+D) word to
occur in x. This establishes contiguity rather than taking it as a premise.
-/
theorem all_windows_occur_implies_subword
    (x p : (ℕ → Option α)) (n k L D : ℕ)
    (hx : KUnique α x n k) (hk : k < L)
    (hocc : ∀ i, i ≤ D → Occurs α x n p i L) :
    ∃ a, a + (L + D) ≤ n ∧ Agree α x a p 0 (L + D) := by
  obtain ⟨a, ha, hzero⟩ := hocc 0 (by omega)
  have aligned : ∀ i, i ≤ D →
      a + i + L ≤ n ∧ Agree α x (a + i) p i L := by
    intro i
    induction i with
    | zero =>
      intro _
      simpa only [Nat.add_zero] using And.intro ha hzero
    | succ i ih =>
      intro hi
      have hprev := ih (by omega)
      obtain ⟨b, hb, hnext⟩ := hocc (i + 1) hi
      have heq := consecutive_occurrences α x p n k L i (a + i) b
        hx hk hprev.1 hb hprev.2 hnext
      constructor
      · omega
      · have hindex : a + (i + 1) = b := by omega
        simpa only [hindex] using hnext
  refine ⟨a, by have hlast := (aligned D le_rfl).1; omega, ?_⟩
  intro j hj
  let i := min j D
  have hiD : i ≤ D := Nat.min_le_right j D
  have hij : i ≤ j := Nat.min_le_left j D
  have hlocal : j - i < L := by
    dsimp [i]
    by_cases h : j ≤ D
    · rw [Nat.min_eq_left h]
      omega
    · rw [Nat.min_eq_right (by omega)]
      omega
  have heq := (aligned i hiD).2 (j - i) hlocal
  have hsource : a + i + (j - i) = a + j := by omega
  have htarget : i + (j - i) = 0 + j := by omega
  simpa only [hsource, htarget] using heq

/-- The full word occurrence is unique; no second root position is needed. -/
theorem subword_position_unique
    (x p : (ℕ → Option α)) (n k m a b : ℕ)
    (hx : KUnique α x n k) (hkm : k ≤ m)
    (ha : a + m ≤ n) (hb : b + m ≤ n)
    (hleft : Agree α x a p 0 m) (hright : Agree α x b p 0 m) :
    a = b := by
  apply hx a b (by omega) (by omega)
  intro i hi
  exact (hleft i (by omega)).trans (hright i (by omega)).symm

end DeletionGeneralization.WordPaths
namespace DeletionGeneralization.SpectrumPath
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

theorem spectrum_boolean {n L : ℕ} (y : Word α n)
    (hy : IsUnique (L-1) (letters y)) :
    ∀ g, spectrum L (letters y) g = 0 ∨ spectrum L (letters y) g = 1 := by
  have hsmall := (unique_iff y).mp hy
  have hlarge : IsUnique L (letters y) := (unique_iff y).mpr (by
    intro a b ha hb hab
    apply hsmall a b (by omega) (by omega)
    intro i hi
    exact hab i (by omega))
  intro g
  have hc := (List.nodup_iff_count_le_one.mp hlarge) (List.ofFn g)
  unfold DeletionHash.MixedEdit.spectrum
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

theorem recovers {n L : ℕ} (y z : Word α n) (hL : 1 ≤ L) (hn : L ≤ n)
    (hy : IsUnique (L-1) (letters y))
    (hs : spectrum L (letters z) = spectrum L (letters y)) : z=y := by
  have hw : ∀ i, i ≤ n-L → WordPaths.Occurs α (OverlapCollision.padBits α y) n
      (OverlapCollision.padBits α z) i L := by
    intro i hi
    have hiL : i+L ≤ n := by omega
    let g : Gram α L := fun j => z ⟨i+j.val, by omega⟩
    have hmem : List.ofFn g ∈ windows L (letters z) :=
      (windows_mem_iff z g).mpr ⟨i, hiL, window_as_ofFn z hiL⟩
    have hz := (nonzero_iff_mem L (letters z) g).mpr hmem
    rw [hs] at hz
    obtain ⟨a, ha, he⟩ := (windows_mem_iff y g).mp ((nonzero_iff_mem L (letters y) g).mp hz)
    rw [window_as_ofFn y ha, List.ofFn_inj] at he
    refine ⟨a, ha, ?_⟩
    intro j hj
    have h := congrFun he (⟨j,hj⟩ : Fin L)
    simpa only [OverlapCollision.padBits, dif_pos (show a+j<n by omega),
      dif_pos (show i+j<n by omega), Option.some.injEq, g] using h
  obtain ⟨a, ha, he⟩ := WordPaths.all_windows_occur_implies_subword α
    (OverlapCollision.padBits α y) (OverlapCollision.padBits α z) n (L-1) L (n-L)
    ((unique_iff y).mp hy) (by omega) hw
  have hl : L+(n-L)=n := by omega
  rw [hl] at ha he
  have ha0 : a=0 := by omega
  subst a
  funext j
  have h := (he j.val j.isLt).symm
  simpa only [OverlapCollision.padBits, Nat.zero_add, dif_pos j.isLt, Option.some.injEq] using h

end DeletionGeneralization.SpectrumPath
namespace DeletionGeneralization.WindowTools
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


end DeletionGeneralization.WindowTools
namespace DeletionGeneralization.RecordWindows
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

end DeletionGeneralization.RecordWindows
namespace DeletionGeneralization.RecordStates
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

end DeletionGeneralization.RecordStates
namespace DeletionGeneralization.SeparatedWindows
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

end DeletionGeneralization.SeparatedWindows
namespace DeletionGeneralization.EditedPrefix
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

end DeletionGeneralization.EditedPrefix
namespace DeletionGeneralization.EditedSuffix
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

end DeletionGeneralization.EditedSuffix
namespace DeletionGeneralization.EditEndpoints
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


end DeletionGeneralization.EditEndpoints
namespace DeletionGeneralization.LocalGeometry
open DeletionHash.MixedEdit SourceLetters EditEndpoints
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

theorem common_windows {n b k L : ℕ} (hb : 1 ≤ b) (hL : L=3*(k+b+1)) (hbk : b<k)
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
  obtain ⟨o,ho,hs⟩ := shared b k (L-1) (by omega) x hx none (some e)
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

end DeletionGeneralization.LocalGeometry
namespace DeletionGeneralization.EditFrame
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

end DeletionGeneralization.EditFrame
namespace DeletionGeneralization.SpectrumContext
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

end DeletionGeneralization.SpectrumContext
namespace DeletionGeneralization.LocalConstruction
open DeletionHash.MixedEdit

universe u

/-- Lemma 2.4: actual flanks and unchanged exterior, full path and length geometry. -/
theorem construct {α : Type u} [Fintype α] [DecidableEq α]
    (n b k L : ℕ) (hq : 2 ≤ Fintype.card α) (hb : 1 ≤ b)
    (hL : L=3*(k+b+1)) (hbk : b<k)
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
    simpa only [oneWord] using SourceLetters.unique_after b k m (by omega) (by omega)
      x hx none (by trivial)
  have hym : IsUnique m y := SourceLetters.unique_after b k m (by omega) (by omega)
    x hx (some e) he
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
    have h := LocalGeometry.common_windows hb hL hbk x hx e he hleft hright ends (a+i) (a+j)
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

end DeletionGeneralization.LocalConstruction

namespace DeletionGeneralization.LocalContext
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

theorem construct [Fintype α] [DecidableEq α]
    (b k L : ℕ) (hq : 2 ≤ Fintype.card α) (hb : 1 ≤ b)
    (hL : L=3*(k+b+1)) (hbk : b<k)
    (W : List α) (hW : IsUnique k W) (e : Edit α)
    (he : ValidEdit b W e) (hl : 2*(L+b) ≤ e.position)
    (hr : e.position+e.removed+2*(L+b) ≤ W.length) :
    ∃ A B X Y : List α,
      W=X++A++window e.removed W e.position++B++Y ∧
      applyEdit e W=X++A++e.replacement++B++Y ∧
      e.position=X.length+A.length ∧ A.length ≤ L-1 ∧ B.length ≤ L-1 ∧
      Bubble k L b (A++window e.removed W e.position++B) (A++e.replacement++B) := by
  let x : Word α W.length := fun i => W.get i
  have hx : letters x=W := by simp [letters,x]
  obtain ⟨A,B,X,Y,h1,h2,h3,_,h4,_,h5,h6,_⟩ :=
    LocalConstruction.construct W.length b k L hq hb hL hbk x (by rwa [hx]) e
      (by rwa [hx]) hl hr
  exact ⟨A,B,X,Y,by simpa only [hx] using h1,by simpa only [hx] using h2,h3,h4,h5,
    by simpa only [hx] using h6⟩

end DeletionGeneralization.LocalContext
namespace DeletionGeneralization.SeparatedBubble
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
  obtain ⟨A,B,X,Y,hframe,hframe',hpos,hA,hB,hbubble⟩ := LocalContext.construct b k L
    hreg.1 hreg.2.2.1 hLg hreg.2.2.2.2.2.1 W hWu e0 he0 (by rfl)
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

end DeletionGeneralization.SeparatedBubble
namespace DeletionGeneralization.SeparatedDisjoint
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
    (hm : 3*k+2*b ≤ m) (x : Word α n) (hx : IsUnique k (letters x))
    (e f : Option (Edit α)) (he : ValidOne b (letters x) e) (hf : ValidOne b (letters x) f)
    (p q i j : ℕ) (hi : i+m ≤ (oneWord (letters x) e).length)
    (hj : j+m ≤ (oneWord (letters x) f).length)
    (hpi : p ≤ i+m) (hip : i ≤ p+b) (hqj : q ≤ j+m) (hjq : j ≤ q+b)
    (hw : window m (oneWord (letters x) e) i=window m (oneWord (letters x) f) j) :
    p ≤ q+2*m+3*b ∧ q ≤ p+2*m+3*b := by
  obtain ⟨o,ho,hs⟩ := shared b k m hm x hx e f he hf i j hi hj hw
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

end DeletionGeneralization.SeparatedDisjoint
namespace DeletionGeneralization.SeparatedCoverage
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
    have hc := positions_close b k (L-1) (by omega) (by omega) x hx e e' he he'
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

end DeletionGeneralization.SeparatedCoverage
open DeletionHash.MixedEdit

universe u

/-- Lemma 2.7: exactly 2t separated edits, returning to the original length. -/
theorem solution {α : Type u} [Fintype α] [DecidableEq α]
    (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (x : Word α n) (hx : IsUnique k (letters x)) (record : List (Edit α))
    (hvalid : ValidRecord b (letters x) record) (hlen : record.length = 2*t)
    (hsep : Separated n t b L record) (htarget : (target (letters x) record).length = n) :
    spectrum L (target (letters x) record) - spectrum L (letters x) ∈ Catalogue k L t b := by exact DeletionGeneralization.SeparatedCoverage.coverage n t b k L hreg x hx record hvalid hlen hsep



#print axioms solution
