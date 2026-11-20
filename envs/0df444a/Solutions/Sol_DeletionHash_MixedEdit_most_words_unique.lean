-- Prove2me | solution 1 for DeletionHash.MixedEdit.most_words_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:41:16.633034+00:00
-- url     : https://prove2.me/submissions/e2802b03-2f0e-4f08-a830-31ed75ed4f32

import Definitions.Def_DeletionHash_MixedEdit_UniqueWords
import Mathlib


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

open DeletionHash.MixedEdit
universe u

private theorem length_eq_clog (q n : ℕ) : uniqueLength q n = 2 * Nat.clog q n + 2 := by
  change 2 * ⌈Real.logb (q : ℝ) (n : ℝ)⌉₊ + 2 = _
  rw [Real.natCeil_logb_natCast]

private theorem eight_choose_le (q n : ℕ) (hq : 2 ≤ q) :
    8 * n.choose 2 ≤ q ^ uniqueLength q n := by
  have hn := Nat.le_pow_clog (show 1<q by omega) n
  have hsq := Nat.mul_le_mul hn hn
  have hchoose : 2 * n.choose 2 ≤ n^2 := by
    rw [Nat.choose_two_right]
    have hdiv := Nat.div_mul_le_self (n * (n-1)) 2
    have hmul := Nat.mul_le_mul_left n (Nat.sub_le n 1)
    nlinarith
  have hq2 : 4 ≤ q^2 := by nlinarith
  have hpow : q ^ uniqueLength q n = (q ^ Nat.clog q n)^2 * q^2 := by
    rw [length_eq_clog, pow_add, show 2 * Nat.clog q n = Nat.clog q n * 2 by omega, pow_mul]
  calc
    8 * n.choose 2 ≤ 4 * n^2 := by omega
    _ ≤ 4 * (q ^ Nat.clog q n)^2 := by nlinarith
    _ ≤ (q ^ Nat.clog q n)^2 * q^2 := by nlinarith
    _ = q ^ uniqueLength q n := hpow.symm

theorem solution {α : Type u} [Fintype α] [DecidableEq α]
    (n : ℕ) (hn : 1 ≤ n) (hq : 2 ≤ Fintype.card α) :
    let q := Fintype.card α
    let k := uniqueLength q n
    let B := (1 - (n.choose 2 : ℝ) / (q : ℝ)^k) * (q : ℝ)^n
    (B ≤ ((uniqueFamily α n k).card : ℝ)) ∧
    ((7:ℝ)/8 * (q : ℝ)^n ≤ B) ∧ ((q : ℝ)^n/2 ≤ (7:ℝ)/8 * (q : ℝ)^n) := by
  letI : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  dsimp
  have hk : 1 ≤ uniqueLength (Fintype.card α) n := by unfold uniqueLength; omega
  have hqpos : (0 : ℝ) < Fintype.card α := by exact_mod_cast (show 0 < Fintype.card α by omega)
  have hp : (0 : ℝ) < (Fintype.card α : ℝ)^uniqueLength (Fintype.card α) n := pow_pos hqpos _
  have hscaled : (8 : ℝ) * n.choose 2 ≤ (Fintype.card α : ℝ)^uniqueLength (Fintype.card α) n := by
    exact_mod_cast eight_choose_le (Fintype.card α) n hq
  have hf : (n.choose 2 : ℝ) / (Fintype.card α : ℝ)^uniqueLength (Fintype.card α) n ≤ 1/8 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [DeletionGeneralization.UniqueBridge.family_eq]
    exact DeletionGeneralization.UniqueWordCount.card_unique_lower_bound_real α n _ hk
  · apply mul_le_mul_of_nonneg_right _ (le_of_lt (pow_pos hqpos n))
    linarith
  · have hnonneg := le_of_lt (pow_pos hqpos n)
    nlinarith

#print axioms solution
