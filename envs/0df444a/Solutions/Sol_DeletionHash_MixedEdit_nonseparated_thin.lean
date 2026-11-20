-- Prove2me | solution 1 for DeletionHash.MixedEdit.nonseparated_thin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:18:13.011594+00:00
-- url     : https://prove2.me/submissions/8b489450-79e4-42a0-8ca9-4f6506797fe9

import Mathlib
import Definitions.Def_DeletionHash_MixedEdit_ConflictGraph
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

namespace DeletionGeneralization.Parity
open DeletionHash.MixedEdit SpectrumPath UniqueBridge
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

theorem distinguishes {n L : ℕ} (x z : Word α n) (hL : 1 ≤ L) (hn : L ≤ n)
    (hx : IsUnique (L-1) (letters x)) (hne : z ≠ x) :
    parity (spectrum L (letters z) - spectrum L (letters x)) ≠ 0 := by
  intro hp
  have hlarge : IsUnique L (letters x) := (unique_iff x).mpr (by
    have hsmall := (unique_iff x).mp hx
    intro a b ha hb hab
    apply hsmall a b (by omega) (by omega)
    intro i hi
    exact hab i (by omega))
  have hsupp : ∀ g : Gram α L, List.ofFn g ∈ windows L (letters x) →
      List.ofFn g ∈ windows L (letters z) := by
    intro g hg
    have hx0 := (nonzero_iff_mem L (letters x) g).mpr hg
    have hx1 : spectrum L (letters x) g = 1 := (spectrum_boolean x hx g).resolve_left hx0
    apply (nonzero_iff_mem L (letters z) g).mp
    intro hz0
    have h := congrFun hp g
    change ((spectrum L (letters z) g - spectrum L (letters x) g : ℤ) : ZMod 2) = 0 at h
    rw [hz0, hx1] at h
    norm_num at h
  have hsub : windows L (letters x) ⊆ windows L (letters z) := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    have hab : a+L ≤ n := by
      simp only [starts, letters, List.length_ofFn, List.mem_range, if_pos hn] at ha
      omega
    rw [window_as_ofFn x hab]
    apply hsupp
    exact (windows_mem_iff x _).mpr ⟨a, hab, window_as_ofFn x hab⟩
  have hperm := (List.Nodup.subperm hlarge hsub).perm_of_length_le (by
    simp only [windows, starts, letters, List.length_map, List.length_range, List.length_ofFn, le_refl])
  apply hne
  apply recovers x z hL hn hx
  funext g
  unfold DeletionHash.MixedEdit.spectrum
  exact_mod_cast (hperm.count_eq (List.ofFn g)).symm

end DeletionGeneralization.Parity
namespace DeletionGeneralization.HashUniform
open DeletionHash.MixedEdit
universe u v
variable {ι : Type u} [Fintype ι] {R r : ℕ}

noncomputable def evaluation (v : Fin R → (ι → ZMod 2)) :
    (ι → Label r) →ₗ[ZMod 2] (Fin R → Label r) :=
  LinearMap.pi (fun i => ∑ g, v i g • LinearMap.proj g)

theorem evaluation_apply (v : Fin R → (ι → ZMod 2)) (ξ : ι → Label r) (i : Fin R) :
    evaluation v ξ i = ∑ g, v i g • ξ g := by
  simp [evaluation]

theorem evaluation_surjective (v : Fin R → (ι → ZMod 2))
    (hv : LinearIndependent (ZMod 2) v) : Function.Surjective (evaluation (r := r) v) := by
  classical
  let f := Fintype.linearCombination (ZMod 2) v
  have hf : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot.mpr hv.fintypeLinearCombination_injective
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective hf
  intro a
  let h : (ι → ZMod 2) →ₗ[ZMod 2] Label r :=
    (Fintype.linearCombination (ZMod 2) a).comp g
  have hvh : ∀ i, h (v i) = a i := by
    intro i
    have he := LinearMap.congr_fun hg (Pi.single i 1)
    have hi : f (Pi.single i 1) = v i := by
      simp [f, Fintype.linearCombination_apply]
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hi] at he
    simp [h, he, Fintype.linearCombination_apply]
  refine ⟨fun j => h (Pi.single j 1), ?_⟩
  funext i
  rw [evaluation_apply, ← hvh i]
  simp_rw [← map_smul]
  rw [← map_sum]
  congr 1
  ext j
  simp [Pi.single_apply, mul_ite]

theorem uniform_fiber {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    [AddCommGroup V] [AddCommGroup W] (f : V →+ W) (hf : Function.Surjective f) (a : W) :
    uniformProbability (fun x => f x = a) = 1 / (Fintype.card W : ℝ) := by
  classical
  have heq : ∀ y : W, Fintype.card {x : V // f x = y} = Fintype.card {x : V // f x = a} := by
    intro y
    simpa only [Fintype.card_subtype] using
      (AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf a))
  have hc : Fintype.card V = Fintype.card W * Fintype.card {x : V // f x = a} := by
    have h := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
    simpa only [Fintype.card_sigma, heq, Finset.sum_const, Finset.card_univ, smul_eq_mul] using h.symm
  have hn : 0 < Fintype.card {x : V // f x = a} := by
    obtain ⟨x,hx⟩ := hf a
    exact Fintype.card_pos_iff.mpr ⟨⟨x,hx⟩⟩
  unfold uniformProbability
  rw [Nat.card_eq_fintype_card, hc, Nat.cast_mul]
  have hne : (Fintype.card {x : V // f x = a} : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp


theorem joint {α : Type u} [Fintype α] [DecidableEq α] {L r R : ℕ}
    (w : Fin R → Spectrum α L)
    (hw : LinearIndependent (ZMod 2) (fun i => parity (w i))) (a : Fin R → Label r) :
    uniformProbability (fun ξ : HashSample α L r => ∀ i, hash ξ (w i) = a i) =
      1 / ((2 : ℝ)^r)^R := by
  classical
  have he : (fun ξ : HashSample α L r => ∀ i, hash ξ (w i) = a i) =
      (fun ξ => evaluation (fun i => parity (w i)) ξ = a) := by
    funext ξ
    simp only [funext_iff, evaluation_apply, DeletionHash.MixedEdit.hash]
  rw [he]
  have h := uniform_fiber (evaluation (r := r) (fun i => parity (w i))).toAddMonoidHom
    (evaluation_surjective _ hw) a
  simpa [Label, Fintype.card_fun, ZMod.card] using h

theorem single {α : Type u} [Fintype α] [DecidableEq α] {L r : ℕ}
    (v : Spectrum α L) (hv : parity v ≠ 0) :
    uniformProbability (fun ξ : HashSample α L r => hash ξ v = 0) = 1 / (2 : ℝ)^r := by
  have hi : LinearIndependent (ZMod 2) (fun _ : Fin 1 => parity v) := by
    rw [linearIndependent_unique_iff]
    exact hv
  simpa using joint (r := r) (fun _ : Fin 1 => v) hi (fun _ => 0)

end DeletionGeneralization.HashUniform

/-!
Counting tuples with an anchor near an endpoint or another anchor. The count
removes one coordinate, records the remaining tuple, and reconstructs the
omitted entry. Each distance constraint allows at most `2 * B` entries.
The right endpoint test is distance to `m`, so no bound on the anchors by `m`
is required. All cardinalities count actual tuples, including repeated anchors.
-/

namespace DeletionGeneralization.ClosePositions

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

/-- An endpoint-near or mutually close tuple of anchors. -/
def Bad {r n : ℕ} (m B : ℕ) (a : Fin r → Fin n) : Prop :=
  (∃ i, (a i).val < B) ∨
  (∃ i, Nat.dist (a i).val m < B) ∨
  (∃ i j, i ≠ j ∧ Nat.dist (a i).val (a j).val < B)

/-- A natural-number ball, intersected with `Fin n`, contains at most `2 * B` points. -/
theorem near_card_le (n c B : ℕ) :
    (univ.filter (fun x : Fin n => Nat.dist x.val c < B)).card ≤ 2 * B := by
  calc
    (univ.filter (fun x : Fin n => Nat.dist x.val c < B)).card ≤
        (range (2 * B)).card := by
      apply Finset.card_le_card_of_injOn (fun x : Fin n => x.val + B - c)
      · intro x hx
        have hd := (mem_filter.mp hx).2
        change x.val + B - c ∈ range (2 * B)
        rw [mem_range]
        unfold Nat.dist at hd
        omega
      · intro x hx y hy heq
        have hx' := (mem_filter.mp hx).2
        have hy' := (mem_filter.mp hy).2
        change x.val + B - c = y.val + B - c at heq
        unfold Nat.dist at hx' hy'
        apply Fin.ext
        omega
    _ = 2 * B := card_range _

/-- Omitting one coordinate leaves exactly `n^r` possible records; each record
admits at most `M` values of the omitted coordinate. -/
theorem coordinate_constraint_card_le {r n : ℕ} (i : Fin (r + 1))
    (P : (Fin r → Fin n) → Fin n → Prop) (M : ℕ)
    (hM : ∀ b, (univ.filter (P b)).card ≤ M) :
    (univ.filter (fun a : Fin (r + 1) → Fin n => P (i.removeNth a) (a i))).card ≤
      M * n ^ r := by
  let fibers : (Fin r → Fin n) → Finset (Fin (r + 1) → Fin n) :=
    fun b => (univ.filter (P b)).image (fun x => i.insertNth x b)
  have hcover :
      univ.filter (fun a : Fin (r + 1) → Fin n => P (i.removeNth a) (a i)) ⊆
        (univ : Finset (Fin r → Fin n)).biUnion fibers := by
    intro a ha
    apply mem_biUnion.mpr
    refine ⟨i.removeNth a, mem_univ _, ?_⟩
    apply mem_image.mpr
    refine ⟨a i, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ha).2⟩, ?_⟩
    exact Fin.insertNth_self_removeNth i a
  calc
    (univ.filter (fun a : Fin (r + 1) → Fin n => P (i.removeNth a) (a i))).card ≤
        ((univ : Finset (Fin r → Fin n)).biUnion fibers).card := card_le_card hcover
    _ ≤ (univ : Finset (Fin r → Fin n)).card * M :=
      card_biUnion_le_card_mul _ fibers M (fun b _ => (card_image_le).trans (hM b))
    _ = M * n ^ r := by simp [Nat.mul_comm]

/-- The reference point may depend on every coordinate except the constrained one. -/
theorem coordinate_near_card_le {r n : ℕ} (i : Fin (r + 1))
    (c : (Fin r → Fin n) → ℕ) (B : ℕ) :
    (univ.filter (fun a : Fin (r + 1) → Fin n =>
      Nat.dist (a i).val (c (i.removeNth a)) < B)).card ≤ (2 * B) * n ^ r := by
  have h := coordinate_constraint_card_le i (fun b x => Nat.dist x.val (c b) < B) (2 * B)
    (fun b => by
      apply le_of_eq_of_le ?_ (near_card_le n (c b) B)
      apply congrArg Finset.card
      ext x
      simp only [mem_filter, mem_univ, true_and])
  apply le_of_eq_of_le ?_ h
  apply congrArg Finset.card
  ext a
  simp only [mem_filter, mem_univ, true_and]

private abbrev EventIndex (r : ℕ) := Fin r × (Fin r ⊕ Bool)

private def Event {r n : ℕ} (m B : ℕ) (q : EventIndex r) (a : Fin r → Fin n) : Prop :=
  match q.2 with
  | .inl j => q.1 ≠ j ∧ Nat.dist (a q.1).val (a j).val < B
  | .inr false => (a q.1).val < B
  | .inr true => Nat.dist (a q.1).val m < B

private theorem event_card_le {r n : ℕ} (m B : ℕ) (q : EventIndex (r + 1)) :
    (univ.filter (Event (n := n) m B q)).card ≤ (2 * B) * n ^ r := by
  rcases q with ⟨i, s⟩
  cases s with
  | inl j =>
      by_cases hij : i = j
      · have hempty : univ.filter (Event (n := n) m B (i, .inl j)) = ∅ := by
          ext a
          simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty]
          change (i ≠ j ∧ Nat.dist (a i).val (a j).val < B) ↔ False
          simp [hij]
        rw [hempty, card_empty]
        exact Nat.zero_le _
      · obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
        apply le_of_eq_of_le ?_
          (coordinate_near_card_le (n := n) i (fun b => (b j').val) B)
        apply congrArg Finset.card
        ext a
        simp only [mem_filter, mem_univ, true_and]
        change (i ≠ j ∧ Nat.dist (a i).val (a j).val < B) ↔
          Nat.dist (a i).val (a (i.succAbove j')).val < B
        rw [hj']
        exact ⟨And.right, fun h => ⟨hij, h⟩⟩
  | inr b =>
      cases b with
      | false =>
          apply le_of_eq_of_le ?_ (coordinate_near_card_le (n := n) i (fun _ => 0) B)
          apply congrArg Finset.card
          ext a
          simp only [mem_filter, mem_univ, true_and]
          change (a i).val < B ↔ Nat.dist (a i).val 0 < B
          rw [Nat.dist_zero_right]
      | true =>
          apply le_of_eq_of_le ?_ (coordinate_near_card_le (n := n) i (fun _ => m) B)
          apply congrArg Finset.card
          ext a
          simp only [mem_filter, mem_univ, true_and]
          rfl

/-- A union bound over all actual endpoint and pair constraints. The exponent
is `r - 1`, and the theorem also covers `r = 0`, `n = 0`, and `B = 0`. -/
theorem bad_card_le (r n m B : ℕ) :
    (univ.filter (Bad (r := r) (n := n) m B)).card ≤
      r * (r + 2) * (2 * B) * n ^ (r - 1) := by
  cases r with
  | zero => simp [Bad]
  | succ r =>
      let events : EventIndex (r + 1) → Finset (Fin (r + 1) → Fin n) :=
        fun q => univ.filter (Event m B q)
      have hcover : univ.filter (Bad (r := r + 1) (n := n) m B) =
          (univ : Finset (EventIndex (r + 1))).biUnion events := by
        ext a
        simp only [mem_filter, mem_univ, true_and, mem_biUnion, events]
        constructor
        · rintro (⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, j, hij, hd⟩)
          · exact ⟨(i, .inr false), hi⟩
          · exact ⟨(i, .inr true), hi⟩
          · exact ⟨(i, .inl j), hij, hd⟩
        · rintro ⟨⟨i, s⟩, h⟩
          cases s with
          | inl j => exact Or.inr (Or.inr ⟨i, j, h⟩)
          | inr b =>
              cases b with
              | false => exact Or.inl ⟨i, h⟩
              | true => exact Or.inr (Or.inl ⟨i, h⟩)
      rw [hcover]
      calc
        ((univ : Finset (EventIndex (r + 1))).biUnion events).card ≤
            (univ : Finset (EventIndex (r + 1))).card * ((2 * B) * n ^ r) :=
          card_biUnion_le_card_mul _ events _ (fun q _ => event_card_le m B q)
        _ = (r + 1) * (r + 1 + 2) * (2 * B) * n ^ (r + 1 - 1) := by
          simp [EventIndex, Fintype.card_prod, Fintype.card_sum, Nat.mul_assoc]


end

end DeletionGeneralization.ClosePositions
namespace DeletionGeneralization.RecordCount
open DeletionHash.MixedEdit
universe u
variable (α : Type u) [Fintype α] [DecidableEq α]

abbrev Tag (b : ℕ) := Fin (b+1) × (Σ l : Fin (b+1), Fin l.val → α)
abbrev Record (b N r : ℕ) := (Fin r → Fin N) × (Fin r → Tag α b)

def decode {b N r : ℕ} (rec : Record α b N r) : List (Edit α) :=
  List.ofFn fun i => ⟨(rec.1 i).val, (rec.2 i).1.val, List.ofFn (rec.2 i).2.2⟩

theorem tag_card_le (b : ℕ) (hq : 1 ≤ Fintype.card α) :
    Fintype.card (Tag α b) ≤ (b+1)^2 * (Fintype.card α)^b := by
  classical
  simp only [Tag, Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma, Fintype.card_fun]
  calc
    (b+1) * (∑ l : Fin (b+1), (Fintype.card α)^l.val) ≤
      (b+1) * (∑ _l : Fin (b+1), (Fintype.card α)^b) := by
        gcongr with l
        omega
    _ = (b+1)^2 * (Fintype.card α)^b := by simp; ring

theorem record_card (b N r : ℕ) :
    Fintype.card (Record α b N r) = N^r * (Fintype.card (Tag α b))^r := by
  simp [Record, Fintype.card_fun]

theorem bad_record_card_le (b N r n B : ℕ) :
    Nat.card {rec : Record α b N r // ClosePositions.Bad n B rec.1} ≤
      r*(r+2)*(2*B)*N^(r-1)*(Fintype.card (Tag α b))^r := by
  classical
  let e : {rec : Record α b N r // ClosePositions.Bad n B rec.1} ≃
      {a : Fin r → Fin N // ClosePositions.Bad n B a} × (Fin r → Tag α b) :=
    { toFun := fun rec => (⟨rec.val.1,rec.property⟩,rec.val.2)
      invFun := fun p => ⟨(p.1.val,p.2),p.1.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_eq_fintype_card, Fintype.card_congr e, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin]
  apply Nat.mul_le_mul_right
  simpa only [Fintype.card_subtype] using ClosePositions.bad_card_le r N n B

theorem edited_length_le (b : ℕ) (x : List α) (e : Edit α) (he : ValidEdit b x e) :
    (applyEdit e x).length ≤ x.length+b := by
  have h1 := he.1
  have h2 := he.2.2.1
  simp only [applyEdit, List.length_append, List.length_take, List.length_drop]
  omega

theorem record_bounds (b : ℕ) (x : List α) (es : List (Edit α)) (he : ValidRecord b x es) :
    ∀ e ∈ es, e.position ≤ x.length+es.length*b ∧
      e.removed ≤ b ∧ e.replacement.length ≤ b := by
  induction es generalizing x with
  | nil => simp
  | cons e es ih =>
    obtain ⟨he,hes⟩ := he
    have hlen := edited_length_le α b x e he
    have hpos := he.1
    have htail := ih (applyEdit e x) hes
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨by simp only [List.length_cons]; omega, he.2.1, he.2.2.1⟩
    · obtain ⟨hp,hr,hl⟩ := htail f hf
      refine ⟨?_,hr,hl⟩
      simp only [List.length_cons]
      nlinarith

theorem encode_exists (b N : ℕ) (es : List (Edit α))
    (he : ∀ e ∈ es, e.position < N ∧ e.removed ≤ b ∧ e.replacement.length ≤ b) :
    ∃ rec : Record α b N es.length, decode α rec = es := by
  let positions : Fin es.length → Fin N := fun i =>
    ⟨(es.get i).position, (he (es.get i) (List.get_mem es i)).1⟩
  let tags : Fin es.length → Tag α b := fun i =>
    (⟨(es.get i).removed, by have h := (he (es.get i) (List.get_mem es i)).2.1; omega⟩,
     ⟨⟨(es.get i).replacement.length, by have h := (he (es.get i) (List.get_mem es i)).2.2; omega⟩,
      fun j => (es.get i).replacement.get j⟩)
  refine ⟨(positions,tags), ?_⟩
  unfold decode
  conv_rhs => rw [← List.ofFn_get es]
  congr 1
  funext i
  simp [positions, tags]


theorem not_separated_bad (n t b L r : ℕ)
    (rec : Record α b (n+2*t*b+1) r) (hnot : ¬ Separated n t b L (decode α rec)) :
    ClosePositions.Bad n (8*(L+t*b)+2*t*b+1) rec.1 := by
  by_contra hbad
  apply hnot
  simp only [ClosePositions.Bad, not_or, not_exists, not_and, not_lt] at hbad
  constructor
  · intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    change 8*(L+t*b) ≤ (rec.1 i).val ∧ (rec.1 i).val+8*(L+t*b) ≤ n
    have hl := hbad.1 i
    have hr := hbad.2.1 i
    have hb := (rec.1 i).isLt
    unfold Nat.dist at hr
    constructor <;> omega
  · intro i j hij
    let i' : Fin r := ⟨i.val, by simpa [decode] using i.isLt⟩
    let j' : Fin r := ⟨j.val, by simpa [decode] using j.isLt⟩
    have hne : i' ≠ j' := by
      intro h
      apply hij
      apply Fin.ext
      simpa only [i', j'] using congrArg (fun z : Fin r => z.val) h
    have h := hbad.2.2 i' j' hne
    have hh : 8*(L+t*b) ≤ Nat.dist (rec.1 i').val (rec.1 j').val := by omega
    change 8*(L+t*b) ≤ Nat.dist ((decode α rec).get i).position ((decode α rec).get j).position
    dsimp only [decode]
    erw [List.get_ofFn, List.get_ofFn]
    exact hh

def decodeWord {b N r n : ℕ} (x : Word α n) (rec : Record α b N r) : Word α n :=
  fun i => (target (letters x) (decode α rec)).getD i.val (x i)

theorem decodeWord_eq {b N r n : ℕ} (x z : Word α n) (rec : Record α b N r)
    (he : target (letters x) (decode α rec) = letters z) : decodeWord α x rec = z := by
  funext i
  change (target (letters x) (decode α rec)).getD i.val (x i) = z i
  rw [he]
  simp [letters, List.getD, i.isLt]

noncomputable def shortPartners {n : ℕ} (t b : ℕ) (x : Word α n) : Finset (Word α n) := by
  classical
  exact (Finset.range (2*t)).biUnion fun r =>
    (Finset.univ : Finset (Record α b (n+2*t*b+1) r)).image (decodeWord α x)

noncomputable def fullPartners {n : ℕ} (t b L : ℕ) (x : Word α n) : Finset (Word α n) := by
  classical
  exact ((Finset.univ : Finset (Record α b (n+2*t*b+1) (2*t))).filter
    (fun rec => ClosePositions.Bad n (8*(L+t*b)+2*t*b+1) rec.1)).image (decodeWord α x)

theorem shortPartners_card_le {n : ℕ} (t b : ℕ) (x : Word α n) :
    (shortPartners α t b x).card ≤
      ∑ r ∈ Finset.range (2*t), (n+2*t*b+1)^r * (Fintype.card (Tag α b))^r := by
  classical
  unfold shortPartners
  apply le_trans Finset.card_biUnion_le
  apply Finset.sum_le_sum
  intro r hr
  exact Finset.card_image_le.trans (by simp [record_card])

theorem fullPartners_card_le {n : ℕ} (t b L : ℕ) (x : Word α n) :
    (fullPartners α t b L x).card ≤
      (2*t)*(2*t+2)*(2*(8*(L+t*b)+2*t*b+1))*(n+2*t*b+1)^(2*t-1)*
        (Fintype.card (Tag α b))^(2*t) := by
  classical
  unfold fullPartners
  apply Finset.card_image_le.trans
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using
    bad_record_card_le α b (n+2*t*b+1) (2*t) n (8*(L+t*b)+2*t*b+1)

theorem partners_cover {n : ℕ} (t b L : ℕ) (x z : Word α n) (es : List (Edit α))
    (hlen : es.length ≤ 2*t) (he : ValidRecord b (letters x) es)
    (hz : target (letters x) es = letters z)
    (hbad : es.length < 2*t ∨ ¬ Separated n t b L es) :
    z ∈ shortPartners α t b x ∪ fullPartners α t b L x := by
  classical
  have hb := record_bounds α b (letters x) es he
  obtain ⟨rec, hrec⟩ := encode_exists α b (n+2*t*b+1) es (by
    intro e he
    obtain ⟨hp,hr,hl⟩ := hb e he
    simp only [letters, List.length_ofFn] at hp
    have hmul := Nat.mul_le_mul_right b hlen
    exact ⟨by omega,hr,hl⟩)
  have hd := decodeWord_eq α x z rec (by rwa [hrec])
  by_cases hshort : es.length < 2*t
  · apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    exact ⟨es.length, Finset.mem_range.mpr hshort, Finset.mem_image.mpr ⟨rec, Finset.mem_univ _, hd⟩⟩
  · have heq : es.length = 2*t := by omega
    obtain ⟨rec', hrec'⟩ : ∃ rec' : Record α b (n+2*t*b+1) (2*t), decode α rec'=es := by
      have aux : ∀ (r : ℕ), es.length=r → ∃ rec' : Record α b (n+2*t*b+1) r, decode α rec'=es := by
        intro r h
        subst r
        exact ⟨rec,hrec⟩
      exact aux (2*t) heq
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨rec', Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, decodeWord_eq α x z rec' (by rwa [hrec'])⟩
    apply not_separated_bad α n t b L (2*t) rec'
    simpa only [hrec'] using hbad.resolve_left hshort


end DeletionGeneralization.RecordCount

namespace DeletionGeneralization.RecordArithmetic
open DeletionHash.MixedEdit RecordCount
universe u

def countConstant (t b : ℕ) : ℕ :=
  (2*t+(2*t)*(2*t+2)*(2*(9+10*t*b))) * (2*t*b+2)^(2*t-1) * (b+1)^(4*t)

theorem countConstant_pos (t b : ℕ) (ht : 1 ≤ t) : 0 < countConstant t b := by
  unfold countConstant
  positivity

theorem short_bound (N T R : ℕ) (hN : 1 ≤ N) (hT : 1 ≤ T) :
    (∑ r ∈ Finset.range R, N^r*T^r) ≤ R*T^R*N^(R-1) := by
  calc
    _ ≤ ∑ _r ∈ Finset.range R, T^R*N^(R-1) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr := Finset.mem_range.mp hr
      calc
        N^r*T^r ≤ N^(R-1)*T^R := by gcongr <;> omega
        _ = T^R*N^(R-1) := Nat.mul_comm _ _
    _ = R*T^R*N^(R-1) := by simp [Nat.mul_assoc]

theorem combined_bound (n t b L T q : ℕ) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (hT : 1 ≤ T) (htag : T ≤ (b+1)^2*q^b) :
    (∑ r ∈ Finset.range (2*t), (n+2*t*b+1)^r*T^r) +
      (2*t)*(2*t+2)*(2*(8*(L+t*b)+2*t*b+1))*(n+2*t*b+1)^(2*t-1)*T^(2*t) ≤
      countConstant t b * L * n^(2*t-1) * q^(2*b*t) := by
  let N := n+2*t*b+1
  let B := 8*(L+t*b)+2*t*b+1
  let K := 9+10*t*b
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hB : B ≤ K*L := by
    dsimp [B,K]
    have h := Nat.mul_le_mul_left (10*t*b) hL
    nlinarith
  have hN' : N ≤ (2*t*b+2)*n := by
    dsimp [N]
    have h := Nat.mul_le_mul_left (2*t*b+1) hn
    nlinarith
  have htag' : T^(2*t) ≤ (b+1)^(4*t)*q^(2*b*t) := by
    calc
      T^(2*t) ≤ ((b+1)^2*q^b)^(2*t) := Nat.pow_le_pow_left htag _
      _ = (b+1)^(4*t)*q^(2*b*t) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]
        congr 1 <;> congr 1 <;> ring
  have hs := short_bound N T (2*t) hN hT
  change (∑ r ∈ Finset.range (2*t), N^r*T^r) +
    (2*t)*(2*t+2)*(2*B)*N^(2*t-1)*T^(2*t) ≤ _
  calc
    _ ≤ (2*t)*T^(2*t)*N^(2*t-1) +
      (2*t)*(2*t+2)*(2*B)*N^(2*t-1)*T^(2*t) := Nat.add_le_add_right hs _
    _ ≤ (2*t)*L*T^(2*t)*N^(2*t-1) +
      (2*t)*(2*t+2)*(2*(K*L))*N^(2*t-1)*T^(2*t) := by
        apply Nat.add_le_add
        · have hR : 2*t ≤ 2*t*L := by simpa using Nat.mul_le_mul_left (2*t) hL
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hR)
        · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
            (Nat.mul_le_mul_left ((2*t)*(2*t+2)) (Nat.mul_le_mul_left 2 hB)))
    _ = (2*t+(2*t)*(2*t+2)*(2*K))*L*N^(2*t-1)*T^(2*t) := by ring
    _ ≤ (2*t+(2*t)*(2*t+2)*(2*K))*L*((2*t*b+2)*n)^(2*t-1)*
      ((b+1)^(4*t)*q^(2*b*t)) := by gcongr
    _ = countConstant t b * L * n^(2*t-1) * q^(2*b*t) := by
      rw [mul_pow]
      unfold countConstant K
      ring

theorem partners_card_le {α : Type u} [Fintype α] [DecidableEq α]
    {n : ℕ} (t b L : ℕ) (x : Word α n) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (hq : 1 ≤ Fintype.card α) :
    (shortPartners α t b x ∪ fullPartners α t b L x).card ≤
      countConstant t b * L * n^(2*t-1) * (Fintype.card α)^(2*b*t) := by
  classical
  have ht : 1 ≤ Fintype.card (Tag α b) := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨(0, ⟨0, Fin.elim0⟩)⟩
  calc
    _ ≤ (shortPartners α t b x).card + (fullPartners α t b L x).card := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add (shortPartners_card_le α t b x) (fullPartners_card_le α t b L x)
    _ ≤ _ := combined_bound n t b L (Fintype.card (Tag α b)) (Fintype.card α)
      hn hL ht (tag_card_le α b hq)

end DeletionGeneralization.RecordArithmetic
namespace DeletionGeneralization.ExceptionalProbability
open DeletionHash.MixedEdit
universe u v

theorem probability_mono {Ω : Type u} [Fintype Ω] {P Q : Ω → Prop}
    (h : ∀ x, P x → Q x) : uniformProbability P ≤ uniformProbability Q := by
  classical
  unfold uniformProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact_mod_cast Fintype.card_le_of_injective
    (fun x : {x // P x} => (⟨x.val,h x.val x.property⟩ : {x // Q x}))
    (fun x y he => Subtype.ext (congrArg (fun z : {x // Q x} => z.val) he))

theorem probability_union {Ω : Type u} [Fintype Ω] {β : Type v}
    (S : Finset β) (P : β → Ω → Prop) :
    uniformProbability (fun x => ∃ z ∈ S, P z x) ≤ ∑ z ∈ S, uniformProbability (P z) := by
  classical
  let E : β → Finset Ω := fun z => Finset.univ.filter (P z)
  have he : Finset.univ.filter (fun x => ∃ z ∈ S, P z x) = S.biUnion E := by
    ext x
    simp [E]
  simp only [uniformProbability, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [he]
  have hc : (S.biUnion E).card ≤ ∑ z ∈ S, (E z).card := Finset.card_biUnion_le
  calc
    ((S.biUnion E).card : ℝ) / Fintype.card Ω ≤
        ((∑ z ∈ S, (E z).card : ℕ) : ℝ) / Fintype.card Ω := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast hc
    _ = _ := by simp only [Nat.cast_sum, Finset.sum_div, E]

theorem hash_sub {α : Type u} [Fintype α] {L r : ℕ}
    (ξ : HashSample α L r) (p q : Spectrum α L) :
    DeletionHash.MixedEdit.hash ξ (p-q) =
      DeletionHash.MixedEdit.hash ξ p - DeletionHash.MixedEdit.hash ξ q := by
  simp [DeletionHash.MixedEdit.hash, parity, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem unique_mono {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    {n k m : ℕ} (x : Word α n) (hk : k ≤ m) (hx : IsUnique k (letters x)) :
    IsUnique m (letters x) := by
  apply (UniqueBridge.unique_iff x).mpr
  intro a b ha hb hab
  apply (UniqueBridge.unique_iff x).mp hx a b (by omega) (by omega)
  intro i hi
  exact hab i (by omega)

theorem collision_bound {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    {n L r : ℕ} (x z : Word α n) (hL : 1 ≤ L) (hn : L ≤ n)
    (hx : IsUnique (L-1) (letters x)) :
    uniformProbability (fun ξ : HashSample α L r =>
      z ≠ x ∧ hash ξ (spectrum L (letters z)) = hash ξ (spectrum L (letters x))) ≤
      1 / (2 : ℝ)^r := by
  classical
  by_cases hne : z=x
  · subst z
    simp [uniformProbability]
  · have hp := Parity.distinguishes x z hL hn hx hne
    have h := HashUniform.single (r := r) (spectrum L (letters z)-spectrum L (letters x)) hp
    simp only [hash_sub, sub_eq_zero] at h
    simpa [hne] using h.le


theorem exceptional_bound {α : Type u} [Fintype α] [DecidableEq α]
    (n t b k L r : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (x : Word α n) (hx : IsUnique k (letters x)) :
    uniformProbability (fun ξ : HashSample α L r => Exceptional n k t b ξ x) ≤
      (RecordArithmetic.countConstant t b : ℝ) * (Fintype.card α : ℝ)^(2*b*t) *
        (L : ℝ) * (n : ℝ)^(2*t-1) / (2 : ℝ)^r := by
  classical
  obtain ⟨hq, ht, hb, hk, hL, hbk, hn⟩ := hreg
  letI : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  have hLpos : 1 ≤ L := by omega
  have hnx : 1 ≤ n := by omega
  have hxm : IsUnique (L-1) (letters x) := unique_mono x (by omega) hx
  let S := RecordCount.shortPartners α t b x ∪ RecordCount.fullPartners α t b L x
  have hcover : ∀ ξ : HashSample α L r, Exceptional n k t b ξ x →
      ∃ z ∈ S, z ≠ x ∧ hash ξ (spectrum L (letters z)) = hash ξ (spectrum L (letters x)) := by
    intro ξ hex
    obtain ⟨_, es, hlen, hvalid, hword, hne, hhash, hbad⟩ := hex
    let y := target (letters x) es
    let z : Word α n := fun i => y.getD i.val (x i)
    have hz : letters z = y := by
      apply List.ext_getElem
      · simp only [letters, List.length_ofFn]
        exact hword.symm
      · intro i hi hj
        simp only [letters, List.getElem_ofFn, z, List.getD,
          List.getElem?_eq_getElem hj, Option.getD_some]
    have hz' : target (letters x) es = letters z := hz.symm
    refine ⟨z, RecordCount.partners_cover α t b L x z es hlen hvalid hz' hbad, ?_, ?_⟩
    · intro heq
      apply hne
      rw [hz', heq]
    · simpa only [hz] using hhash
  have hcard : (S.card : ℝ) ≤
      (RecordArithmetic.countConstant t b : ℝ) * L * (n : ℝ)^(2*t-1) *
        (Fintype.card α : ℝ)^(2*b*t) := by
    exact_mod_cast RecordArithmetic.partners_card_le t b L x hnx hLpos (by omega)
  calc
    _ ≤ uniformProbability (fun ξ : HashSample α L r =>
      ∃ z ∈ S, z ≠ x ∧ hash ξ (spectrum L (letters z)) = hash ξ (spectrum L (letters x))) :=
        probability_mono hcover
    _ ≤ ∑ z ∈ S, uniformProbability (fun ξ : HashSample α L r =>
      z ≠ x ∧ hash ξ (spectrum L (letters z)) = hash ξ (spectrum L (letters x))) := probability_union _ _
    _ ≤ ∑ _z ∈ S, 1 / (2 : ℝ)^r := by
      apply Finset.sum_le_sum
      intro z hz
      exact collision_bound x z hLpos hn hxm
    _ = (S.card : ℝ) / (2 : ℝ)^r := by simp [div_eq_mul_inv]
    _ ≤ ((RecordArithmetic.countConstant t b : ℝ) * L * (n : ℝ)^(2*t-1) *
        (Fintype.card α : ℝ)^(2*b*t)) / (2 : ℝ)^r :=
      div_le_div_of_nonneg_right hcard (by positivity)
    _ = _ := by ring


end DeletionGeneralization.ExceptionalProbability
open DeletionHash.MixedEdit

universe u

/-- Lemma 3.4: c precedes every alphabet, length and label dimension. -/
theorem solution (t b : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ b) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) (α : Type u) [Fintype α] [DecidableEq α],
      Fintype.card α = q → ∀ n k L r : ℕ, Regime q n t b k L → 1 ≤ r →
      ∀ x : Word α n, IsUnique k (letters x) →
      uniformProbability (fun ξ : HashSample α L r => Exceptional n k t b ξ x) ≤
        c * (q : ℝ)^(2*b*t) * (L : ℝ) * (n : ℝ)^(2*t-1) / (2 : ℝ)^r := by
  refine ⟨(DeletionGeneralization.RecordArithmetic.countConstant t b : ℝ), ?_, ?_⟩
  · exact_mod_cast DeletionGeneralization.RecordArithmetic.countConstant_pos t b (by omega)
  · intro q α instF instD hc n k L r hreg hr x hx
    subst q
    exact DeletionGeneralization.ExceptionalProbability.exceptional_bound n t b k L r hreg x hx



#print axioms solution
