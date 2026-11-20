-- Prove2me | solution 1 for DeletionHash.MixedEdit.connected_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:57:22.803325+00:00
-- url     : https://prove2.me/submissions/25407abb-755d-4e12-9329-920e2ea713f4

import Definitions.Def_DeletionHash_MixedEdit_Bubbles
import Definitions.Def_DeletionHash_MixedEdit_Paths
import Definitions.Def_DeletionHash_MixedEdit_Regime
import Definitions.Def_DeletionHash_MixedEdit_SupportComponents
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
namespace DeletionGeneralization.BubbleSupport
open DeletionHash.MixedEdit WindowTools
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem mem_windows (x : List α) (k i : ℕ) (hi : i+k ≤ x.length) :
    window k x i ∈ windows k x := by
  apply List.mem_map.mpr
  refine ⟨i,?_,rfl⟩
  simp only [starts,List.mem_range,if_pos (show k ≤ x.length by omega)]
  omega

theorem occurrence {L : ℕ} (P : List α) (hP : SpellsSimplePath L P) (g : Gram α L)
    (hg : List.ofFn g ∈ windows L P) :
    ∃ i, i+L ≤ P.length ∧ List.ofFn g=window L P i ∧
      List.ofFn (gramPrefix g)=window (L-1) P i ∧
      List.ofFn (gramSuffix g)=window (L-1) P (i+1) := by
  obtain ⟨i,hi,hgi⟩ := List.mem_map.mp hg
  obtain ⟨g',hg',hp,hs⟩ := hP.2.1 i hi
  have he : g'=g := List.ofFn_inj.mp (hg'.trans hgi)
  subst g'
  refine ⟨i,?_,hgi.symm,hp,hs⟩
  simp only [starts,List.mem_range] at hi
  split_ifs at hi <;> omega

theorem window_last (P : List α) (m : ℕ) (hm : m ≤ P.length) :
    window m P (P.length-m)=P.drop (P.length-m) := by
  unfold window
  apply List.take_of_length_le
  simp only [List.length_drop]
  omega

theorem prefix_not_last {L : ℕ} (P : List α) (hP : SpellsSimplePath L P) (hL : 1 ≤ L)
    (g : Gram α L) (hg : List.ofFn g ∈ windows L P) :
    List.ofFn (gramPrefix g) ≠ P.drop (P.length-(L-1)) := by
  obtain ⟨i,hi,hg,hpre,hsuf⟩ := occurrence P hP g hg
  intro he
  have hm : L-1 ≤ P.length := by omega
  have h := unique_positions.mp hP.1 i (P.length-(L-1)) (by omega) (by omega)
    (hpre.symm.trans (he.trans (window_last P (L-1) hm).symm))
  omega

theorem suffix_not_first {L : ℕ} (P : List α) (hP : SpellsSimplePath L P) (hL : 1 ≤ L)
    (g : Gram α L) (hg : List.ofFn g ∈ windows L P) :
    List.ofFn (gramSuffix g) ≠ P.take (L-1) := by
  obtain ⟨i,hi,hg,hpre,hsuf⟩ := occurrence P hP g hg
  intro he
  have h := unique_positions.mp hP.1 (i+1) 0 (by omega) (by omega)
    (by simpa only [window,List.drop_zero] using hsuf.symm.trans he)
  omega

theorem endpoint_mem {L : ℕ} (P : List α) (hP : SpellsSimplePath L P) (hL : 1 ≤ L)
    (g : Gram α L) (hg : List.ofFn g ∈ windows L P) :
    gramPrefix g ∈ PathVertices L P ∧ gramSuffix g ∈ PathVertices L P := by
  obtain ⟨i,hi,hg,hpre,hsuf⟩ := occurrence P hP g hg
  constructor
  · change List.ofFn (gramPrefix g) ∈ windows (L-1) P
    rw [hpre]
    exact mem_windows P (L-1) i (by omega)
  · change List.ofFn (gramSuffix g) ∈ windows (L-1) P
    rw [hsuf]
    exact mem_windows P (L-1) (i+1) (by omega)

theorem gram_spans_whole {L : ℕ} (P : List α) (hP : SpellsSimplePath L P) (hL : 1 ≤ L)
    (g : Gram α L) (hg : List.ofFn g ∈ windows L P)
    (hp : List.ofFn (gramPrefix g)=P.take (L-1))
    (hs : List.ofFn (gramSuffix g)=P.drop (P.length-(L-1))) :
    List.ofFn g=P := by
  obtain ⟨i,hi,hg,hpre,hsuf⟩ := occurrence P hP g hg
  have hi0 : i=0 := unique_positions.mp hP.1 i 0 (by omega) (by omega)
    (by simpa only [window,List.drop_zero] using hpre.symm.trans hp)
  have hiend := unique_positions.mp hP.1 (i+1) (P.length-(L-1)) (by omega) (by omega)
    (hsuf.symm.trans (hs.trans (window_last P (L-1) (by omega)).symm))
  have hlen : P.length=L := by omega
  simpa only [hi0,window,List.drop_zero,← hlen,List.take_length] using hg

theorem bubble_words_ne {k L b : ℕ} {P Q : List α} (hB : Bubble k L b P Q) : P ≠ Q := by
  obtain ⟨A,U,V,B,hP,hQ,hne,_⟩ := hB.1
  intro he
  rw [hP,hQ] at he
  exact hne (by simpa using he)

theorem bubble_grams_disjoint {k L b : ℕ} {P Q : List α}
    (hB : Bubble k L b P Q) (hL : 1 ≤ L) (g : Gram α L) :
    ¬ (List.ofFn g ∈ windows L P ∧ List.ofFn g ∈ windows L Q) := by
  intro ⟨hgP,hgQ⟩
  obtain ⟨hform,hPl,hPu,hQl,hQu,hfirst,hlast,hpathP,hpathQ,hmeet⟩ := hB
  have ep := endpoint_mem P hpathP hL g hgP
  have eq := endpoint_mem Q hpathQ hL g hgQ
  have hp := hmeet (gramPrefix g) ep.1 eq.1
  have hs := hmeet (gramSuffix g) ep.2 eq.2
  have hp' : List.ofFn (gramPrefix g)=P.take (L-1) :=
    hp.resolve_right (prefix_not_last P hpathP hL g hgP)
  have hs' : List.ofFn (gramSuffix g)=P.drop (P.length-(L-1)) :=
    hs.resolve_left (suffix_not_first P hpathP hL g hgP)
  have hP := gram_spans_whole P hpathP hL g hgP hp' hs'
  have hQ := gram_spans_whole Q hpathQ hL g hgQ (hp'.trans hfirst) (hs'.trans hlast)
  apply bubble_words_ne ⟨hform,hPl,hPu,hQl,hQu,hfirst,hlast,hpathP,hpathQ,hmeet⟩
  exact hP.symm.trans hQ

theorem spectrum_boolean {L : ℕ} (P : List α) (hP : SpellsSimplePath L P) :
    ∀ g, spectrum L P g=0 ∨ spectrum L P g=1 := by
  have hlarge : IsUnique L P := unique_positions.mpr (by
    intro i j hi hj he
    apply unique_positions.mp hP.1 i j (by omega) (by omega)
    have h := congrArg (List.take (L-1)) he
    simpa only [window,List.take_take,Nat.min_eq_left (show L-1 ≤ L by omega)] using h)
  intro g
  have h := List.nodup_iff_count_le_one.mp hlarge (List.ofFn g)
  unfold DeletionHash.MixedEdit.spectrum
  omega


theorem nonzero_iff_mem (L : ℕ) (P : List α) (g : Gram α L) :
    spectrum L P g ≠ 0 ↔ List.ofFn g ∈ windows L P := by
  simp [DeletionHash.MixedEdit.spectrum,List.count_eq_zero]

theorem difference_support {k L b : ℕ} {P Q : List α} (hB : Bubble k L b P Q)
    (hL : 1 ≤ L) (g : Gram α L) :
    (spectrum L Q-spectrum L P) g ≠ 0 ↔
      List.ofFn g ∈ windows L P ∨ List.ofFn g ∈ windows L Q := by
  have hcopy := hB
  obtain ⟨_,_,_,_,_,_,_,hP,hQ,_⟩ := hcopy
  have hp := spectrum_boolean P hP g
  have hq := spectrum_boolean Q hQ g
  have hn := bubble_grams_disjoint hB hL g
  rw [← nonzero_iff_mem L P g,← nonzero_iff_mem L Q g] at hn ⊢
  change (spectrum L Q g-spectrum L P g ≠ 0) ↔ _
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> simp_all

theorem difference_values {k L b : ℕ} {P Q : List α} (hB : Bubble k L b P Q)
    (g : Gram α L) :
    (spectrum L Q-spectrum L P) g=0 ∨
      (spectrum L Q-spectrum L P) g=1 ∨ (spectrum L Q-spectrum L P) g= -1 := by
  have hcopy := hB
  obtain ⟨_,_,_,_,_,_,_,hP,hQ,_⟩ := hcopy
  have hp := spectrum_boolean P hP g
  have hq := spectrum_boolean Q hQ g
  change spectrum L Q g-spectrum L P g=0 ∨
    spectrum L Q g-spectrum L P g=1 ∨ spectrum L Q g-spectrum L P g= -1
  omega

theorem difference_endpoint {k L b : ℕ} {P Q : List α} (hB : Bubble k L b P Q)
    (hL : 1 ≤ L) (g : Gram α L) (hg : (spectrum L Q-spectrum L P) g ≠ 0) :
    gramPrefix g ∈ bubbleVertices L P Q ∧ gramSuffix g ∈ bubbleVertices L P Q := by
  have hcopy := hB
  obtain ⟨_,_,_,_,_,_,_,hP,hQ,_⟩ := hcopy
  rcases (difference_support hB hL g).mp hg with hg | hg
  · have he := endpoint_mem P hP hL g hg
    exact ⟨Or.inl he.1,Or.inl he.2⟩
  · have he := endpoint_mem Q hQ hL g hg
    exact ⟨Or.inr he.1,Or.inr he.2⟩


end DeletionGeneralization.BubbleSupport
namespace DeletionGeneralization.CatalogueSupport
open DeletionHash.MixedEdit BubbleSupport
universe u v
variable {α : Type u} [Fintype α] [DecidableEq α]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

theorem distinct_piece_zero {k L b : ℕ} (B : ι → List α × List α)
    (hB : ∀ i, Bubble k L b (B i).1 (B i).2)
    (hdis : ∀ i j, i ≠ j → Disjoint (bubbleVertices L (B i).1 (B i).2)
      (bubbleVertices L (B j).1 (B j).2))
    (hL : 1 ≤ L) (i j : ι) (hij : i ≠ j) (g : Gram α L)
    (hi : (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0) :
    (spectrum L (B j).2-spectrum L (B j).1) g = 0 := by
  by_contra hj
  have hp := (difference_endpoint (hB i) hL g hi).1
  have hq := (difference_endpoint (hB j) hL g hj).1
  exact Set.disjoint_left.mp (hdis i j hij) hp hq

theorem sum_piece_eq {k L b : ℕ} (B : ι → List α × List α)
    (hB : ∀ i, Bubble k L b (B i).1 (B i).2)
    (hdis : ∀ i j, i ≠ j → Disjoint (bubbleVertices L (B i).1 (B i).2)
      (bubbleVertices L (B j).1 (B j).2))
    (hL : 1 ≤ L) (i : ι) (g : Gram α L)
    (hi : (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0) :
    (∑ j, (spectrum L (B j).2-spectrum L (B j).1)) g =
      (spectrum L (B i).2-spectrum L (B i).1) g := by
  rw [Finset.sum_apply]
  apply Finset.sum_eq_single i
  · intro j hj hji
    exact distinct_piece_zero B hB hdis hL i j hji.symm g hi
  · simp

theorem sum_support {k L b : ℕ} (B : ι → List α × List α)
    (hB : ∀ i, Bubble k L b (B i).1 (B i).2)
    (hdis : ∀ i j, i ≠ j → Disjoint (bubbleVertices L (B i).1 (B i).2)
      (bubbleVertices L (B j).1 (B j).2))
    (hL : 1 ≤ L) (g : Gram α L) :
    (∑ j, (spectrum L (B j).2-spectrum L (B j).1)) g ≠ 0 ↔
      ∃ j, (spectrum L (B j).2-spectrum L (B j).1) g ≠ 0 := by
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    apply h
    rw [Finset.sum_apply]
    exact Finset.sum_eq_zero (fun i hi => hn i)
  · rintro ⟨i,hi⟩
    rwa [sum_piece_eq B hB hdis hL i g hi]

theorem catalogue_values {k L t b : ℕ} (w : Spectrum α L)
    (hw : w ∈ Catalogue k L t b) (hL : 1 ≤ L) (g : Gram α L) :
    w g=0 ∨ w g=1 ∨ w g= -1 := by
  obtain ⟨B,hB,hdis,rfl⟩ := hw
  by_cases hn : ∃ i, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0
  · obtain ⟨i,hi⟩ := hn
    rw [sum_piece_eq B hB hdis hL i g hi]
    exact difference_values (hB i) g
  · left
    push_neg at hn
    rw [Finset.sum_apply]
    exact Finset.sum_eq_zero (fun i hi => hn i)

theorem parity_zero_iff {k L t b : ℕ} (w : Spectrum α L)
    (hw : w ∈ Catalogue k L t b) (hL : 1 ≤ L) (g : Gram α L) :
    parity w g=0 ↔ w g=0 := by
  rcases catalogue_values w hw hL g with h | h | h <;> simp [parity,h]

theorem relation_support_subset {k L t b : ℕ} (w : Spectrum α L)
    (hw : w ∈ Catalogue k L t b) (hL : 1 ≤ L) (I : Finset (Spectrum α L))
    (hrel : parity w=∑ z ∈ I, parity z) :
    supportUnion {w} ⊆ supportUnion I := by
  intro g hg
  obtain ⟨v,hv,hvg⟩ := hg
  have hvw : v=w := Finset.mem_singleton.mp hv
  subst v
  by_contra hnone
  have hz : ∀ z ∈ I, z g=0 := by
    intro z hz
    by_contra hzg
    exact hnone ⟨z,hz,hzg⟩
  have hp : parity w g ≠ 0 := by
    intro hp
    exact hvg ((parity_zero_iff w hw hL g).mp hp)
  apply hp
  have hc := congrFun hrel g
  simp only [Finset.sum_apply] at hc
  rw [hc]
  apply Finset.sum_eq_zero
  intro z hzi
  simp [parity,hz z hzi]

end DeletionGeneralization.CatalogueSupport
namespace DeletionGeneralization.SupportPaths
open DeletionHash.MixedEdit BubbleSupport WindowTools
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem mem_starts (P : List α) (L i : ℕ) (hi : i+L ≤ P.length) : i ∈ starts L P := by
  simp only [starts,List.mem_range,if_pos (show L ≤ P.length by omega)]
  omega

theorem vertices_incident {L : ℕ} (F : Finset (Spectrum α L)) (P : List α)
    (hP : SpellsSimplePath L P) (hL : 1 ≤ L) (hlen : L ≤ P.length)
    (hedges : ∀ g, List.ofFn g ∈ windows L P → g ∈ supportUnion F)
    (v : Gram α (L-1)) (hv : v ∈ PathVertices L P) : v ∈ incidentVertices F := by
  obtain ⟨i,hi,he⟩ := List.mem_map.mp hv
  have him : i+(L-1) ≤ P.length := by
    simp only [starts,List.mem_range,if_pos (show L-1 ≤ P.length by omega)] at hi
    omega
  by_cases hil : i+L ≤ P.length
  · obtain ⟨g,hg,hpre,hsuf⟩ := hP.2.1 i (mem_starts P L i hil)
    refine ⟨g,hedges g (by rw [hg]; exact mem_windows P L i hil),Or.inl ?_⟩
    exact List.ofFn_inj.mp (he.symm.trans hpre.symm)
  · have hipos : 1 ≤ i := by omega
    have hib : i-1+L ≤ P.length := by omega
    obtain ⟨g,hg,hpre,hsuf⟩ := hP.2.1 (i-1) (mem_starts P L (i-1) hib)
    have hidx : i-1+1=i := by omega
    rw [hidx] at hsuf
    refine ⟨g,hedges g (by rw [hg]; exact mem_windows P L (i-1) hib),Or.inr ?_⟩
    exact List.ofFn_inj.mp (he.symm.trans hsuf.symm)

theorem edge_reachable {L : ℕ} (F : Finset (Spectrum α L))
    (v w : {v : Gram α (L-1) // v ∈ incidentVertices F}) (g : Gram α L)
    (hg : g ∈ supportUnion F) (hv : v.val=gramPrefix g) (hw : w.val=gramSuffix g) :
    (supportGraph F).Reachable v w := by
  classical
  by_cases he : v=w
  · subst w
    exact SimpleGraph.Reachable.refl _
  · apply SimpleGraph.Adj.reachable
    exact ⟨he,g,hg,Or.inl ⟨hv,hw⟩⟩

def gramAt (P : List α) (i k : ℕ) (hi : i+k ≤ P.length) : Gram α k :=
  fun j => P[i+j.val]'(by omega)

theorem ofFn_gramAt (P : List α) (i k : ℕ) (hi : i+k ≤ P.length) :
    List.ofFn (gramAt P i k hi)=window k P i := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,window,List.length_take,List.length_drop]
    omega
  · intro j hj hk
    simp only [List.getElem_ofFn,gramAt,window,List.getElem_take,List.getElem_drop]


theorem path_connected {L : ℕ} (F : Finset (Spectrum α L)) (P : List α)
    (hP : SpellsSimplePath L P) (hL : 1 ≤ L) (hlen : L ≤ P.length)
    (hedges : ∀ g, List.ofFn g ∈ windows L P → g ∈ supportUnion F)
    (v w : {v : Gram α (L-1) // v ∈ incidentVertices F})
    (hv : v.val ∈ PathVertices L P) (hw : w.val ∈ PathVertices L P) :
    (supportGraph F).Reachable v w := by
  let m := L-1
  let N := P.length-m+1
  have hN : 1 ≤ N := by dsimp [N]; omega
  let V : Fin N → {v : Gram α (L-1) // v ∈ incidentVertices F} := fun q =>
    ⟨gramAt P q.val m (by have h := q.isLt; dsimp [N] at h; omega),
      vertices_incident F P hP hL hlen hedges _ (by
        change List.ofFn (gramAt P q.val m (by have h := q.isLt; dsimp [N] at h; omega)) ∈ windows m P
        rw [ofFn_gramAt]
        exact mem_windows P m q.val (by have h := q.isLt; dsimp [N] at h; omega))⟩
  have hstep : ∀ q (hq : q+1<N),
      (supportGraph F).Reachable (V ⟨q,by omega⟩) (V ⟨q+1,hq⟩) := by
    intro q hq
    have hqL : q+L ≤ P.length := by dsimp [N,m] at hq; omega
    obtain ⟨g,hg,hpre,hsuf⟩ := hP.2.1 q (mem_starts P L q hqL)
    apply edge_reachable F _ _ g (hedges g (by rw [hg]; exact mem_windows P L q hqL))
    · apply List.ofFn_inj.mp
      change List.ofFn (gramAt P q m (by dsimp [m]; omega)) = List.ofFn (gramPrefix g)
      rw [ofFn_gramAt]
      exact hpre.symm
    · apply List.ofFn_inj.mp
      change List.ofFn (gramAt P (q+1) m (by dsimp [m]; omega)) = List.ofFn (gramSuffix g)
      rw [ofFn_gramAt]
      exact hsuf.symm
  have hreach : ∀ q (hq : q<N),
      (supportGraph F).Reachable (V ⟨0,by omega⟩) (V ⟨q,hq⟩) := by
    intro q
    induction q with
    | zero =>
      intro hq
      exact SimpleGraph.Reachable.refl _
    | succ q ih =>
      intro hq
      exact (ih (by omega)).trans (hstep q hq)
  have hcover : ∀ z : {v : Gram α (L-1) // v ∈ incidentVertices F},
      z.val ∈ PathVertices L P → ∃ q, V q=z := by
    intro z hz
    obtain ⟨i,hi,he⟩ := List.mem_map.mp hz
    have hib : i+m ≤ P.length := by
      simp only [starts,List.mem_range,if_pos (show L-1 ≤ P.length by omega)] at hi
      dsimp [m]
      omega
    refine ⟨⟨i,by dsimp [N]; omega⟩,Subtype.ext ?_⟩
    apply List.ofFn_inj.mp
    change List.ofFn (gramAt P i m hib)=List.ofFn z.val
    rw [ofFn_gramAt]
    exact he
  obtain ⟨i,hi⟩ := hcover v hv
  obtain ⟨j,hj⟩ := hcover w hw
  rw [← hi,← hj]
  exact (hreach i.val i.isLt).symm.trans (hreach j.val j.isLt)


end DeletionGeneralization.SupportPaths
namespace DeletionGeneralization.BubbleConnectivity
open DeletionHash.MixedEdit BubbleSupport SupportPaths
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem bubble_connected {k L b : ℕ} (F : Finset (Spectrum α L)) (P Q : List α)
    (hB : Bubble k L b P Q) (hL : 1 ≤ L)
    (hsupport : ∀ g, (spectrum L Q-spectrum L P) g ≠ 0 → g ∈ supportUnion F) :
    ∃ r : {v : Gram α (L-1) // v ∈ incidentVertices F},
      r.val ∈ bubbleVertices L P Q ∧
      ∀ v : {v : Gram α (L-1) // v ∈ incidentVertices F},
        v.val ∈ bubbleVertices L P Q → (supportGraph F).Reachable r v := by
  have hcopy := hB
  obtain ⟨_,hPl,_,hQl,_,hfirst,_,hpathP,hpathQ,_⟩ := hcopy
  have hedgesP : ∀ g, List.ofFn g ∈ windows L P → g ∈ supportUnion F := by
    intro g hg
    exact hsupport g ((difference_support hB hL g).mpr (Or.inl hg))
  have hedgesQ : ∀ g, List.ofFn g ∈ windows L Q → g ∈ supportUnion F := by
    intro g hg
    exact hsupport g ((difference_support hB hL g).mpr (Or.inr hg))
  let v0 := gramAt P 0 (L-1) (by omega)
  have hvP : v0 ∈ PathVertices L P := by
    change List.ofFn v0 ∈ windows (L-1) P
    rw [ofFn_gramAt]
    exact mem_windows P (L-1) 0 (by omega)
  have hvQ : v0 ∈ PathVertices L Q := by
    change List.ofFn v0 ∈ windows (L-1) Q
    have h : List.ofFn v0=Q.take (L-1) := by
      rw [ofFn_gramAt]
      simpa only [window,List.drop_zero] using hfirst
    rw [h]
    simpa only [window,List.drop_zero] using mem_windows Q (L-1) 0 (by omega)
  let r : {v : Gram α (L-1) // v ∈ incidentVertices F} :=
    ⟨v0,vertices_incident F P hpathP hL hPl hedgesP v0 hvP⟩
  refine ⟨r,Or.inl hvP,?_⟩
  intro v hv
  rcases hv with hv | hv
  · exact path_connected F P hpathP hL hPl hedgesP r v hvP hv
  · exact path_connected F Q hpathQ hL hQl hedgesQ r v hvQ hv

theorem bubble_nonzero {k L b : ℕ} (P Q : List α)
    (hB : Bubble k L b P Q) (hL : 1 ≤ L) :
    ∃ g, (spectrum L Q-spectrum L P) g ≠ 0 := by
  have hPl : L ≤ P.length := hB.2.1
  let g := gramAt P 0 L (by omega)
  refine ⟨g,(difference_support hB hL g).mpr (Or.inl ?_)⟩
  rw [ofFn_gramAt]
  exact mem_windows P L 0 (by omega)

theorem bubble_vertices_eq {k L b : ℕ} (P Q : List α)
    (hB : Bubble k L b P Q) (hL : 1 ≤ L) :
    bubbleVertices L P Q=incidentVertices {spectrum L Q-spectrum L P} := by
  ext v
  constructor
  · intro hv
    have hcopy := hB
    obtain ⟨_,hPl,_,hQl,_,_,_,hP,hQ,_⟩ := hcopy
    rcases hv with hv | hv
    · apply vertices_incident _ P hP hL hPl _ v hv
      intro g hg
      exact ⟨_,Finset.mem_singleton_self _,(difference_support hB hL g).mpr (Or.inl hg)⟩
    · apply vertices_incident _ Q hQ hL hQl _ v hv
      intro g hg
      exact ⟨_,Finset.mem_singleton_self _,(difference_support hB hL g).mpr (Or.inr hg)⟩
  · rintro ⟨g,⟨z,hz,hg⟩,hv⟩
    have he : z=spectrum L Q-spectrum L P := Finset.mem_singleton.mp hz
    subst z
    have hends := difference_endpoint hB hL g hg
    rcases hv with rfl | rfl
    · exact hends.1
    · exact hends.2

end DeletionGeneralization.BubbleConnectivity
namespace DeletionGeneralization.ComponentCover
open DeletionHash.MixedEdit BubbleSupport BubbleConnectivity CatalogueSupport
universe u v
variable {α : Type u} [Fintype α] [DecidableEq α]
variable {ι : Type v} [Fintype ι]

theorem cover_by_bubbles {k L b : ℕ} (F : Finset (Spectrum α L))
    (B : ι → List α × List α) (hB : ∀ i, Bubble k L b (B i).1 (B i).2)
    (hL : 1 ≤ L)
    (hsupport : ∀ i g, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0 → g ∈ supportUnion F)
    (hcover : ∀ g ∈ supportUnion F, ∃ i, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0) :
    ∃ r : ι → {v : Gram α (L-1) // v ∈ incidentVertices F},
      (∀ i, (r i).val ∈ bubbleVertices L (B i).1 (B i).2) ∧
      (∀ i (v : {v : Gram α (L-1) // v ∈ incidentVertices F}),
        v.val ∈ bubbleVertices L (B i).1 (B i).2 → (supportGraph F).Reachable (r i) v) ∧
      Function.Surjective (fun i => (supportGraph F).connectedComponentMk (r i)) := by
  classical
  choose r hr hreach using fun i => bubble_connected F (B i).1 (B i).2 (hB i) hL (hsupport i)
  refine ⟨r,hr,hreach,?_⟩
  intro C
  refine SimpleGraph.ConnectedComponent.ind ?_ C
  intro v
  obtain ⟨g,hg,hv⟩ := v.property
  obtain ⟨i,hi⟩ := hcover g hg
  have he := difference_endpoint (hB i) hL g hi
  have hvmem : v.val ∈ bubbleVertices L (B i).1 (B i).2 := by
    rcases hv with hv | hv
    · rw [hv]
      exact he.1
    · rw [hv]
      exact he.2
  exact ⟨i,SimpleGraph.ConnectedComponent.sound (hreach i v hvmem)⟩

theorem count_le_bubbles {k L b : ℕ} (F : Finset (Spectrum α L))
    (B : ι → List α × List α) (hB : ∀ i, Bubble k L b (B i).1 (B i).2)
    (hL : 1 ≤ L)
    (hsupport : ∀ i g, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0 → g ∈ supportUnion F)
    (hcover : ∀ g ∈ supportUnion F, ∃ i, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0) :
    componentCount F ≤ Fintype.card ι := by
  classical
  obtain ⟨r,hr,hreach,hsurj⟩ := cover_by_bubbles F B hB hL hsupport hcover
  have h := Nat.card_le_card_of_surjective _ hsurj
  simpa only [componentCount,Nat.card_eq_fintype_card] using h

theorem catalogue_count_le {k L t b : ℕ} (w : Spectrum α L)
    (hw : w ∈ Catalogue k L t b) (hL : 1 ≤ L) :
    componentCount {w} ≤ 2*t := by
  classical
  obtain ⟨B,hB,hdis,heq⟩ := hw
  have hsupport : ∀ i g, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0 →
      g ∈ supportUnion {w} := by
    intro i g hg
    refine ⟨w,Finset.mem_singleton_self _,?_⟩
    rw [heq]
    exact (sum_support B hB hdis hL g).mpr ⟨i,hg⟩
  have hcover : ∀ g ∈ supportUnion {w},
      ∃ i, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0 := by
    rintro g ⟨z,hz,hg⟩
    have hz : z=w := Finset.mem_singleton.mp hz
    subst z
    rw [heq] at hg
    exact (sum_support B hB hdis hL g).mp hg
  simpa only [Fintype.card_fin] using count_le_bubbles {w} B hB hL hsupport hcover

end DeletionGeneralization.ComponentCover
namespace DeletionGeneralization.ComponentInsert
open DeletionHash.MixedEdit BubbleSupport BubbleConnectivity CatalogueSupport
universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem support_mono {L : ℕ} {F H : Finset (Spectrum α L)} (h : F ⊆ H) :
    supportUnion F ⊆ supportUnion H := by
  rintro g ⟨w,hw,hg⟩
  exact ⟨w,h hw,hg⟩

theorem incident_mono {L : ℕ} {F H : Finset (Spectrum α L)} (h : F ⊆ H) :
    incidentVertices F ⊆ incidentVertices H := by
  rintro v ⟨g,hg,hv⟩
  exact ⟨g,support_mono h hg,hv⟩

def inclusion {L : ℕ} {F H : Finset (Spectrum α L)} (h : F ⊆ H) :
    supportGraph F →g supportGraph H where
  toFun v := ⟨v.val,incident_mono h v.property⟩
  map_rel' := by
    rintro v z ⟨hne,g,hg,he⟩
    refine ⟨?_,g,support_mono h hg,he⟩
    intro hvz
    exact hne (Subtype.ext (congrArg (fun x : {v : Gram α (L-1) // v ∈ incidentVertices H} => x.val) hvz))

theorem insert_bound {k L t b : ℕ} (hL : 1 ≤ L) (ht : 1 ≤ t)
    (F : Finset (Spectrum α L)) (w : Spectrum α L) (hw : w ∈ Catalogue k L t b)
    (hadj : ∃ z ∈ F, RuleAdjacent w z) :
    componentCount (insert w F) ≤ componentCount F+(2*t-1) := by
  classical
  let H := insert w F
  have hsub : F ⊆ H := Finset.subset_insert _ _
  let φ := inclusion hsub
  obtain ⟨B,hB,hdis,heq⟩ := hw
  have hs : ∀ i g, (spectrum L (B i).2-spectrum L (B i).1) g ≠ 0 → g ∈ supportUnion H := by
    intro i g hg
    refine ⟨w,Finset.mem_insert_self _ _,?_⟩
    rw [heq]
    exact (sum_support B hB hdis hL g).mpr ⟨i,hg⟩
  choose r hr hreach using fun i => bubble_connected H (B i).1 (B i).2 (hB i) hL (hs i)
  let f : (supportGraph F).ConnectedComponent ⊕ Fin (2*t) → (supportGraph H).ConnectedComponent :=
    Sum.elim (fun C => C.map φ) (fun i => (supportGraph H).connectedComponentMk (r i))
  have hsurj : Function.Surjective f := by
    intro C
    refine SimpleGraph.ConnectedComponent.ind ?_ C
    intro v
    obtain ⟨g,⟨z,hz,hg⟩,hv⟩ := v.property
    rcases Finset.mem_insert.mp hz with hzw | hz
    · subst z
      rw [heq] at hg
      obtain ⟨i,hi⟩ := (sum_support B hB hdis hL g).mp hg
      have he := difference_endpoint (hB i) hL g hi
      have hvmem : v.val ∈ bubbleVertices L (B i).1 (B i).2 := by
        rcases hv with hv | hv
        · rw [hv]; exact he.1
        · rw [hv]; exact he.2
      exact ⟨Sum.inr i,SimpleGraph.ConnectedComponent.sound (hreach i v hvmem)⟩
    · let vF : {v : Gram α (L-1) // v ∈ incidentVertices F} := ⟨v.val,⟨g,⟨z,hz,hg⟩,hv⟩⟩
      refine ⟨Sum.inl ((supportGraph F).connectedComponentMk vF),?_⟩
      rfl
  have hnot : ¬Function.Injective f := by
    obtain ⟨z,hz,v,hvw,hvz⟩ := hadj
    have hvF : v ∈ incidentVertices F :=
      incident_mono (Finset.singleton_subset_iff.mpr hz) hvz
    let vF : {v : Gram α (L-1) // v ∈ incidentVertices F} := ⟨v,hvF⟩
    obtain ⟨g,⟨z',hz',hg⟩,hv⟩ := hvw
    have hz' : z'=w := Finset.mem_singleton.mp hz'
    subst z'
    rw [heq] at hg
    obtain ⟨i,hi⟩ := (sum_support B hB hdis hL g).mp hg
    have he := difference_endpoint (hB i) hL g hi
    have hvmem : (φ vF).val ∈ bubbleVertices L (B i).1 (B i).2 := by
      change v ∈ bubbleVertices L (B i).1 (B i).2
      rcases hv with hv | hv
      · rw [hv]; exact he.1
      · rw [hv]; exact he.2
    have heqC : f (Sum.inr i)=f (Sum.inl ((supportGraph F).connectedComponentMk vF)) :=
      SimpleGraph.ConnectedComponent.sound (hreach i (φ vF) hvmem)
    intro hinj
    have h := hinj heqC
    cases h
  letI : Fintype (supportGraph F).ConnectedComponent := Fintype.ofFinite _
  letI : Fintype (supportGraph H).ConnectedComponent := Fintype.ofFinite _
  have hc := Fintype.card_lt_of_surjective_not_injective f hsurj hnot
  simp only [Fintype.card_sum,Fintype.card_fin] at hc
  have heF : Fintype.card (supportGraph F).ConnectedComponent=componentCount F := by
    simp [componentCount,Nat.card_eq_fintype_card]
  have heH : Fintype.card (supportGraph H).ConnectedComponent=componentCount (insert w F) := by
    simp [H,componentCount,Nat.card_eq_fintype_card]
  rw [heF,heH] at hc
  omega

end DeletionGeneralization.ComponentInsert
namespace DeletionGeneralization.ConnectedBlocks
open DeletionHash.MixedEdit ComponentInsert ComponentCover
universe u v
variable {α : Type u} [Fintype α] [DecidableEq α]

theorem reachable_mem {V : Type v} (G : SimpleGraph V) (S : Set V)
    (hclosed : ∀ v ∈ S, ∀ w, G.Adj v w → w ∈ S)
    {v w : V} (hv : v ∈ S) (h : G.Reachable v w) : w ∈ S := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hv
  | cons he p ih => exact ih (hclosed _ hv _ he)

theorem connected_bound {k L t b : ℕ} (hL : 1 ≤ L) (ht : 1 ≤ t)
    (B : Finset (Spectrum α L)) (hB : ∀ z ∈ B, z ∈ Catalogue k L t b)
    (hconn : ConnectedRules B) :
    componentCount B ≤ (2*t-1)*B.card+1 := by
  classical
  let S := B.powerset.filter (fun F => F.Nonempty ∧ componentCount F ≤ (2*t-1)*F.card+1)
  obtain ⟨z,hz⟩ := hconn.1
  have hseed : {z} ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hz),Finset.singleton_nonempty z,?_⟩
    have hc := catalogue_count_le z (hB z hz) hL
    simp only [Finset.card_singleton,mul_one]
    omega
  obtain ⟨F,hF,hmax⟩ := Finset.exists_max_image S Finset.card ⟨{z},hseed⟩
  have hfdata := Finset.mem_filter.mp hF
  have hsub : F ⊆ B := Finset.mem_powerset.mp hfdata.1
  have hne := hfdata.2.1
  have hbound := hfdata.2.2
  have hclosed : ∀ v : {w : Spectrum α L // w ∈ B}, v.val ∈ F →
      ∀ w : {w : Spectrum α L // w ∈ B}, (ruleGraph B).Adj v w → w.val ∈ F := by
    intro v hv w hadj
    by_contra hw
    have hnewbound : componentCount (insert w.val F) ≤ (2*t-1)*(insert w.val F).card+1 := by
      have ha : ∃ z ∈ F, RuleAdjacent w.val z := by
        refine ⟨v.val,hv,?_⟩
        obtain ⟨p,hp,hq⟩ := hadj.2
        exact ⟨p,hq,hp⟩
      have hc := insert_bound hL ht F w.val (hB w.val w.property) ha
      rw [Finset.card_insert_of_notMem hw,Nat.mul_add,Nat.mul_one]
      omega
    have hnew : insert w.val F ∈ S := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr ?_,Finset.insert_nonempty _ _,hnewbound⟩
      exact Finset.insert_subset w.property hsub
    have hm := hmax _ hnew
    rw [Finset.card_insert_of_notMem hw] at hm
    omega
  obtain ⟨v,hv⟩ := hne
  have hBF : B ⊆ F := by
    intro w hw
    exact reachable_mem (ruleGraph B) {z | z.val ∈ F} hclosed hv
      (hconn.2 ⟨v,hsub hv⟩ ⟨w,hw⟩)
  have heq : F=B := Finset.Subset.antisymm hsub hBF
  rwa [heq] at hbound

theorem blocks (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L) :
    (∀ F : Finset (Spectrum α L), (∀ z ∈ F, z ∈ Catalogue k L t b) →
      ∀ w : Spectrum α L, w ∈ Catalogue k L t b → w ∉ F →
        (∃ z ∈ F, RuleAdjacent w z) →
        componentCount (insert w F) ≤ componentCount F+(2*t-1)) ∧
    (∀ B : Finset (Spectrum α L), (∀ z ∈ B, z ∈ Catalogue k L t b) →
      ConnectedRules B → componentCount B ≤ (2*t-1)*B.card+1) := by
  have ht : 1 ≤ t := by have h := hreg.2.1; omega
  have hL : 1 ≤ L := by have h := hreg.2.2.2.2.1; omega
  exact ⟨fun F _ w hw _ ha => insert_bound hL ht F w hw ha,
    fun B hB hconn => connected_bound hL ht B hB hconn⟩

end DeletionGeneralization.ConnectedBlocks
open DeletionHash.MixedEdit

universe u

/-- Lemma 4.5, both the adjunction estimate and its nonempty connected-set consequence. -/
theorem solution {α : Type u} [Fintype α] [DecidableEq α]
    (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L) :
    (∀ F : Finset (Spectrum α L), (∀ z ∈ F, z ∈ Catalogue k L t b) →
      ∀ w : Spectrum α L, w ∈ Catalogue k L t b → w ∉ F →
        (∃ z ∈ F, RuleAdjacent w z) →
        componentCount (insert w F) ≤ componentCount F + (2*t-1)) ∧
    (∀ B : Finset (Spectrum α L), (∀ z ∈ B, z ∈ Catalogue k L t b) →
      ConnectedRules B → componentCount B ≤ (2*t-1)*B.card+1) := by exact DeletionGeneralization.ConnectedBlocks.blocks n t b k L hreg



#print axioms solution
