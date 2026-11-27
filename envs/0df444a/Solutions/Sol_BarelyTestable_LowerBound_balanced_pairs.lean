-- Prove2me | solution 1 for BarelyTestable.LowerBound.balanced_pairs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:26:34.591793+00:00
-- url     : https://prove2.me/submissions/9c08b5b3-aeae-47d9-a6c9-d5fcde2d381c

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Loads

set_option autoImplicit false

open BarelyTestable.LowerBound NonmonotoneSubmod.Shared MeasureTheory

namespace BTHelper_balanced_pairs

open Finset

/-- Exponential versus polynomial growth: `4096·27·m⁴·16^m ≤ 27^m` for `m ≥ 60`. -/
lemma arith_base (m : ℕ) (hm : 60 ≤ m) : 4096 * m ^ 4 * 16 ^ m * 27 ≤ 27 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : 8 * (n + 1) ≤ 9 * n := by omega
    have h2 : (8 * (n + 1)) ^ 4 ≤ (9 * n) ^ 4 := Nat.pow_le_pow_left h1 4
    have h3 : 16 * (n + 1) ^ 4 ≤ 27 * n ^ 4 := by
      have : 4096 * (n + 1) ^ 4 ≤ 6561 * n ^ 4 := by
        have e1 : (8 * (n + 1)) ^ 4 = 4096 * (n + 1) ^ 4 := by ring
        have e2 : (9 * n) ^ 4 = 6561 * n ^ 4 := by ring
        omega
      generalize (n + 1) ^ 4 = a at this ⊢
      generalize n ^ 4 = b at this ⊢
      omega
    calc 4096 * (n + 1) ^ 4 * 16 ^ (n + 1) * 27
        = 4096 * 27 * 16 ^ n * (16 * (n + 1) ^ 4) := by ring
      _ ≤ 4096 * 27 * 16 ^ n * (27 * n ^ 4) := Nat.mul_le_mul_left _ h3
      _ = (4096 * n ^ 4 * 16 ^ n * 27) * 27 := by ring
      _ ≤ 27 ^ n * 27 := Nat.mul_le_mul_right _ ih
      _ = 27 ^ (n + 1) := by ring

/-- If `3m - 3 ≤ 4j` then `8m·2^m ≤ 3^j` (for `m ≥ 60`). -/
lemma key_bound (m j : ℕ) (hm : 60 ≤ m) (hj : 3 * m - 3 ≤ 4 * j) :
    8 * m * 2 ^ m ≤ 3 ^ j := by
  have hb := arith_base m hm
  have h27 : (27 : ℕ) ^ m = 3 ^ (3 * m - 3) * 27 := by
    rw [show (27 : ℕ) = 3 ^ 3 by norm_num, ← pow_mul, ← pow_add]
    congr 1; omega
  have h1 : (8 * m * 2 ^ m) ^ 4 ≤ 3 ^ (3 * m - 3) := by
    have e : (8 * m * 2 ^ m) ^ 4 = 4096 * m ^ 4 * 16 ^ m := by
      rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]; ring
    rw [e]
    have : 4096 * m ^ 4 * 16 ^ m * 27 ≤ 3 ^ (3 * m - 3) * 27 := h27 ▸ hb
    omega
  have h2 : 3 ^ (3 * m - 3) ≤ (3 ^ j) ^ 4 := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact (Nat.pow_le_pow_iff_left (by norm_num : (4 : ℕ) ≠ 0)).mp (h1.trans h2)

/-- Generating-function tail bound, lower tail. -/
lemma low_count (m : ℕ) (hm : 60 ≤ m) :
    (univ.filter (fun S : Finset (Fin m) => 4 * S.card ≤ m + 3)).card * (8 * m) ≤ 2 ^ m := by
  have hsum : ∑ S : Finset (Fin m), 3 ^ (m - S.card) = 4 ^ m := by
    have := Finset.sum_pow_mul_eq_add_pow (1 : ℕ) 3 (univ : Finset (Fin m))
    simp only [one_pow, one_mul, Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at this
    rw [this]
  have h1 : (univ.filter (fun S : Finset (Fin m) => 4 * S.card ≤ m + 3)).card * (8 * m * 2 ^ m)
      ≤ 4 ^ m := by
    rw [← hsum, Finset.card_eq_sum_ones, Finset.sum_mul]
    calc ∑ S ∈ univ.filter (fun S : Finset (Fin m) => 4 * S.card ≤ m + 3), 1 * (8 * m * 2 ^ m)
        ≤ ∑ S ∈ univ.filter (fun S : Finset (Fin m) => 4 * S.card ≤ m + 3), 3 ^ (m - S.card) := by
          apply Finset.sum_le_sum
          intro S hS
          simp only [Finset.mem_filter] at hS
          have hc : S.card ≤ m := by simpa using Finset.card_le_univ S
          rw [one_mul]; exact key_bound m _ hm (by omega)
      _ ≤ ∑ S : Finset (Fin m), 3 ^ (m - S.card) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; positivity)
  have h4 : (4 : ℕ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
  rw [h4] at h1
  have hp : 0 < 2 ^ m := by positivity
  have : (univ.filter (fun S : Finset (Fin m) => 4 * S.card ≤ m + 3)).card * (8 * m) * 2 ^ m
      ≤ 2 ^ m * 2 ^ m := by rw [mul_assoc]; exact h1
  exact Nat.le_of_mul_le_mul_right this hp

/-- Generating-function tail bound, upper tail. -/
lemma high_count (m : ℕ) (hm : 60 ≤ m) :
    (univ.filter (fun S : Finset (Fin m) => 4 * (m - S.card) ≤ m + 3)).card * (8 * m) ≤ 2 ^ m := by
  have hsum : ∑ S : Finset (Fin m), 3 ^ S.card = 4 ^ m := by
    have := Finset.sum_pow_mul_eq_add_pow (3 : ℕ) 1 (univ : Finset (Fin m))
    simp only [one_pow, mul_one, Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at this
    rw [this]
  have h1 : (univ.filter (fun S : Finset (Fin m) => 4 * (m - S.card) ≤ m + 3)).card *
      (8 * m * 2 ^ m) ≤ 4 ^ m := by
    rw [← hsum, Finset.card_eq_sum_ones, Finset.sum_mul]
    calc ∑ S ∈ univ.filter (fun S : Finset (Fin m) => 4 * (m - S.card) ≤ m + 3), 1 * (8 * m * 2 ^ m)
        ≤ ∑ S ∈ univ.filter (fun S : Finset (Fin m) => 4 * (m - S.card) ≤ m + 3), 3 ^ S.card := by
          apply Finset.sum_le_sum
          intro S hS
          simp only [Finset.mem_filter] at hS
          have hc : S.card ≤ m := by simpa using Finset.card_le_univ S
          rw [one_mul]; exact key_bound m _ hm (by omega)
      _ ≤ ∑ S : Finset (Fin m), 3 ^ S.card :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; positivity)
  have h4 : (4 : ℕ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
  rw [h4] at h1
  have hp : 0 < 2 ^ m := by positivity
  have : (univ.filter (fun S : Finset (Fin m) => 4 * (m - S.card) ≤ m + 3)).card * (8 * m) * 2 ^ m
      ≤ 2 ^ m * 2 ^ m := by rw [mul_assoc]; exact h1
  exact Nat.le_of_mul_le_mul_right this hp

/-- The set of "bad" block subsets. -/
def bad (m : ℕ) : Finset (Finset (Fin m)) :=
  univ.filter (fun S : Finset (Fin m) => 4 * S.card ≤ m + 3 ∨ 4 * (m - S.card) ≤ m + 3)

lemma bad_count (m : ℕ) (hm : 60 ≤ m) : (bad m).card * (4 * m) ≤ 2 ^ m := by
  have h1 := low_count m hm
  have h2 := high_count m hm
  have h3 : (bad m).card ≤ (univ.filter (fun S : Finset (Fin m) => 4 * S.card ≤ m + 3)).card +
      (univ.filter (fun S : Finset (Fin m) => 4 * (m - S.card) ≤ m + 3)).card := by
    unfold bad; rw [Finset.filter_or]; exact Finset.card_union_le _ _
  nlinarith

/-- `HalfSet m` is the same as a family of `m` blocks. -/
def blockEquiv (m : ℕ) : HalfSet m ≃ (Fin m → Finset (Fin m)) where
  toFun X := fun i => block X i
  invFun f := univ.filter (fun p : Fin m × Fin m => p.2 ∈ f p.1)
  left_inv X := by ext ⟨i, j⟩; simp [block]
  right_inv f := by funext i; ext j; simp [block]

lemma pi_count (m : ℕ) (i : Fin m) (T : Finset (Finset (Fin m))) :
    (univ.filter (fun f : Fin m → Finset (Fin m) => f i ∈ T)).card * 2 ^ m =
      T.card * 2 ^ (m * m) := by
  classical
  have hf : univ.filter (fun f : Fin m → Finset (Fin m) => f i ∈ T) =
      Fintype.piFinset (Function.update (fun _ => (univ : Finset (Finset (Fin m)))) i T) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h j
      by_cases hj : j = i
      · subst hj; simpa using h
      · simp [Function.update_of_ne hj]
    · intro h; simpa using h i
  rw [hf, Fintype.card_piFinset]
  rw [show (∏ j, (Function.update (fun _ => (univ : Finset (Finset (Fin m)))) i T j).card) =
      ∏ j, Function.update (fun _ => (univ : Finset (Finset (Fin m))).card) i T.card j by
    apply Finset.prod_congr rfl; intro j _
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
  have hc : (univ \ {i} : Finset (Fin m)).card = m - 1 := by
    rw [Finset.card_sdiff]; simp
  rw [hc, mul_assoc, ← pow_mul, ← pow_add]
  congr 2
  have : 1 ≤ m := by have := i.2; omega
  rcases m with _ | m
  · omega
  · simp; ring

lemma halfset_count (m : ℕ) (i : Fin m) (T : Finset (Finset (Fin m))) :
    (univ.filter (fun X : HalfSet m => block X i ∈ T)).card * 2 ^ m = T.card * 2 ^ (m * m) := by
  rw [← pi_count m i T]
  congr 1
  apply Finset.card_bij (fun X _ => blockEquiv m X)
  · intro X hX; simpa [blockEquiv] using hX
  · intro X _ Y _ h; exact (blockEquiv m).injective h
  · intro f hf
    refine ⟨(blockEquiv m).symm f, ?_, by simp⟩
    have : blockEquiv m ((blockEquiv m).symm f) i ∈ T := by simpa using hf
    simpa [blockEquiv] using this

lemma not_balanced (m : ℕ) (X : HalfSet m) (h : ¬ BarelyTestable.LowerBound.Balanced X) :
    ∃ i, block X i ∈ bad m := by
  unfold BarelyTestable.LowerBound.Balanced at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  refine ⟨i, ?_⟩
  have hc : (block X i).card ≤ m := by simpa using Finset.card_le_univ (block X i)
  simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h1 : (m : ℝ) / 4 + 1 ≤ (block X i).card
  · have h2 := hi h1
    right
    have : (3 * m : ℝ) < 4 * (block X i).card + 4 := by linarith
    have : 3 * m < 4 * (block X i).card + 4 := by exact_mod_cast this
    omega
  · left
    push Not at h1
    have : (4 * (block X i).card : ℝ) < m + 4 := by linarith
    have : 4 * (block X i).card < m + 4 := by exact_mod_cast this
    omega

open Classical in
lemma unbalanced_count (m : ℕ) (hm : 60 ≤ m) :
    4 * (univ.filter (fun X : HalfSet m => ¬ BarelyTestable.LowerBound.Balanced X)).card ≤ 2 ^ (m * m) := by
  classical
  have hsub : univ.filter (fun X : HalfSet m => ¬ BarelyTestable.LowerBound.Balanced X) ⊆
      univ.biUnion (fun i : Fin m => univ.filter (fun X : HalfSet m => block X i ∈ bad m)) := by
    intro X hX
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX
    obtain ⟨i, hi⟩ := not_balanced m X hX
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨i, hi⟩
  have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 : (∑ i : Fin m, (univ.filter (fun X : HalfSet m => block X i ∈ bad m)).card) * 2 ^ m
      = m * ((bad m).card * 2 ^ (m * m)) := by
    rw [Finset.sum_mul]
    simp only [halfset_count]
    simp
  have h3 := bad_count m hm
  have hp : 0 < 2 ^ m := by positivity
  have h4 : 4 * (univ.filter (fun X : HalfSet m => ¬ BarelyTestable.LowerBound.Balanced X)).card * 2 ^ m ≤
      2 ^ (m * m) * 2 ^ m := by
    calc 4 * (univ.filter (fun X : HalfSet m => ¬ BarelyTestable.LowerBound.Balanced X)).card * 2 ^ m
        ≤ 4 * ((∑ i : Fin m, (univ.filter (fun X : HalfSet m => block X i ∈ bad m)).card) * 2 ^ m) := by
          rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h1)
      _ = ((bad m).card * (4 * m)) * 2 ^ (m * m) := by rw [h2]; ring
      _ ≤ 2 ^ m * 2 ^ (m * m) := Nat.mul_le_mul_right _ h3
      _ = 2 ^ (m * m) * 2 ^ m := by ring
  exact Nat.le_of_mul_le_mul_right h4 hp

open Classical in
lemma balanced_count (m : ℕ) (hm : 60 ≤ m) :
    3 * 2 ^ (m * m) ≤ 4 * (univ.filter (fun X : HalfSet m => BarelyTestable.LowerBound.Balanced X)).card := by
  classical
  have h := unbalanced_count m hm
  have hs := Finset.card_filter_add_card_filter_not (s := (univ : Finset (HalfSet m)))
    (fun X => BarelyTestable.LowerBound.Balanced X)
  have hc : (univ : Finset (HalfSet m)).card = 2 ^ (m * m) := by
    simp [Fintype.card_finset]
  omega

end BTHelper_balanced_pairs

open BTHelper_balanced_pairs in
theorem solution :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → (2 : ℝ)^(2*m^2) / 2 ≤ balancedPairs m := by
  classical
  refine ⟨60, fun m hm => ?_⟩
  have hb := balanced_count m hm
  have hp : balancedPairs m =
      (Finset.univ.filter (fun X : HalfSet m => BarelyTestable.LowerBound.Balanced X)).card ^ 2 := by
    unfold balancedPairs
    rw [← Finset.univ_product_univ]
    rw [Finset.filter_product (fun X : HalfSet m => BarelyTestable.LowerBound.Balanced X) (fun X : HalfSet m => BarelyTestable.LowerBound.Balanced X)]
    rw [Finset.card_product, sq]
  rw [hp]
  set B := (Finset.univ.filter (fun X : HalfSet m => BarelyTestable.LowerBound.Balanced X)).card
  have hbR : (3 : ℝ) * 2 ^ (m * m) ≤ 4 * (B : ℝ) := by exact_mod_cast hb
  have hpos : (0 : ℝ) ≤ 2 ^ (m * m) := by positivity
  have he : (2 : ℝ) ^ (2 * m ^ 2) = (2 ^ (m * m)) ^ 2 := by rw [← pow_mul]; ring_nf
  rw [he]
  push_cast
  nlinarith
