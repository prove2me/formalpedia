-- Prove2me | solution 1 for BarelyTestable.LowerBound.load_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:28:14.087067+00:00
-- url     : https://prove2.me/submissions/116ed74c-14c6-4ff5-8d73-75646b5852e0

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Loads
import Theorems.Thm_BarelyTestable_LowerBound_block_sums

set_option autoImplicit false

open BarelyTestable.LowerBound NonmonotoneSubmod.Shared MeasureTheory

namespace BTHelper_load_second_moment

open Finset

/-! ### Uniform means -/

section Mean
variable {α : Type} [Fintype α] [Nonempty α]

lemma uniformMean_sum {ι : Type} (s : Finset ι) (f : ι → α → ℝ) :
    uniformMean (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, uniformMean (f i) := by
  unfold uniformMean; rw [Finset.sum_comm, Finset.sum_div]

lemma uniformMean_mul_left (c : ℝ) (f : α → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f := by
  unfold uniformMean; rw [← Finset.mul_sum, mul_div_assoc]

lemma uniformMean_mono {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    uniformMean f ≤ uniformMean g := by
  unfold uniformMean
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (Nat.cast_nonneg _)

/-- Second moment of a nonnegative combination of random variables whose pairwise
correlations are bounded by `p·[i = j] + q`. -/
lemma uniformMean_sq_le {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (I : ι → α → ℝ) (p q : ℝ)
    (hI : ∀ i j, uniformMean (fun a => I i a * I j a) ≤ (if i = j then p else 0) + q) :
    uniformMean (fun a => (∑ i, w i * I i a) ^ 2) ≤
      p * ∑ i, w i ^ 2 + q * (∑ i, w i) ^ 2 := by
  have h1 : (fun a => (∑ i, w i * I i a) ^ 2) =
      fun a => ∑ i, ∑ j, (w i * w j) * (I i a * I j a) := by
    funext a; rw [sq, Finset.sum_mul_sum]; congr 1; funext i; congr 1; funext j; ring
  rw [h1, uniformMean_sum]
  simp_rw [uniformMean_sum, uniformMean_mul_left]
  calc ∑ i, ∑ j, w i * w j * uniformMean (fun a => I i a * I j a)
      ≤ ∑ i, ∑ j, w i * w j * ((if i = j then p else 0) + q) := by
        gcongr with i _ j _
        · exact mul_nonneg (hw i) (hw j)
        · exact hI i j
    _ = p * ∑ i, w i ^ 2 + q * (∑ i, w i) ^ 2 := by
        simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]
        rw [sq (∑ i, w i), Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum]
        congr 1
        · congr 1; funext i; ring
        · congr 1; funext i; rw [Finset.mul_sum]; congr 1; funext j; ring

end Mean

/-! ### Counting functions with prescribed values -/

section Count
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

lemma card_filter_agree (s : Finset α) (g : α → β) :
    (univ.filter (fun f : α → β => ∀ x ∈ s, f x = g x)).card * Fintype.card β ^ s.card =
      Fintype.card β ^ Fintype.card α := by
  have hfil : univ.filter (fun f : α → β => ∀ x ∈ s, f x = g x) =
      Fintype.piFinset (fun x => if x ∈ s then ({g x} : Finset β) else univ) := by
    ext f
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h x; split_ifs with hx
      · simp [h x hx]
      · simp
    · intro h x hx; simpa [hx] using h x
  rw [hfil, Fintype.card_piFinset]
  have h2 : Fintype.card β ^ s.card = ∏ x, (if x ∈ s then Fintype.card β else 1) := by
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  rw [h2, ← Finset.prod_mul_distrib, ← Finset.card_univ (α := α), ← Finset.prod_const]
  refine Finset.prod_congr rfl fun x _ => ?_
  split_ifs <;> simp

lemma uniformMean_agree [Nonempty β] (s : Finset α) (g : α → β) :
    uniformMean (fun f : α → β => if ∀ x ∈ s, f x = g x then (1 : ℝ) else 0) =
      1 / (Fintype.card β : ℝ) ^ s.card := by
  unfold uniformMean
  rw [Finset.sum_boole, Fintype.card_fun]
  have h := card_filter_agree s g
  have hpos : (0 : ℝ) < (Fintype.card β : ℝ) ^ s.card := by
    have : 0 < Fintype.card β := Fintype.card_pos
    positivity
  have h' : ((univ.filter (fun f : α → β => ∀ x ∈ s, f x = g x)).card : ℝ) *
      (Fintype.card β : ℝ) ^ s.card = (Fintype.card β : ℝ) ^ Fintype.card α := by
    exact_mod_cast h
  have hne : ((univ.filter (fun f : α → β => ∀ x ∈ s, f x = g x)).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr ⟨g, by simp⟩).ne'
  rw [Nat.cast_pow, ← h']
  field_simp

/-- Correlation of two point-evaluation indicators of a uniformly random function. -/
lemma uniformMean_ind_mul [Nonempty β] (a a' : α) (b b' : β) :
    uniformMean (fun f : α → β => (if f a = b then (1 : ℝ) else 0) *
      (if f a' = b' then (1 : ℝ) else 0)) ≤
      (if a = a' then 1 / (Fintype.card β : ℝ) else 0) + 1 / (Fintype.card β : ℝ) ^ 2 := by
  have hpos : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  by_cases haa : a = a'
  · subst haa
    have h := uniformMean_agree (α := α) {a} (fun _ => b)
    simp only [mem_singleton, forall_eq, card_singleton, pow_one] at h
    rw [if_pos rfl]
    calc _ ≤ uniformMean (fun f : α → β => if f a = b then (1 : ℝ) else 0) := by
            apply uniformMean_mono; intro f; split_ifs <;> norm_num
      _ = _ := h
      _ ≤ _ := by have : (0:ℝ) ≤ 1 / (Fintype.card β : ℝ) ^ 2 := by positivity
                  linarith
  · rw [if_neg haa, zero_add]
    have h := uniformMean_agree (α := α) {a, a'} (fun x => if x = a then b else b')
    rw [Finset.card_pair haa] at h
    rw [← h]
    apply le_of_eq; congr 1; funext f
    have : (∀ x ∈ ({a, a'} : Finset α), f x = if x = a then b else b') ↔ (f a = b ∧ f a' = b') := by
      simp [Ne.symm haa]
    rw [if_congr this rfl rfl, ite_zero_mul_ite_zero, one_mul]

end Count

/-! ### Blocks -/

section Blocks
variable {m : ℕ}

lemma block_union (X G : HalfSet m) (i : Fin m) : block (X ∪ G) i = block X i ∪ block G i := by
  ext j; simp [block]

lemma block_sdiff (X G : HalfSet m) (i : Fin m) : block (X \ G) i = block X i \ block G i := by
  ext j; simp [block]

lemma block_xorSet (X G : HalfSet m) (i : Fin m) :
    block (xorSet X G) i = xorSet (block X i) (block G i) := by
  simp only [xorSet, block_union, block_sdiff]

lemma block_selected (γ : Selector m) (i : Fin m) : block (selected γ) i = {γ i} := by
  ext j; simp [block, selected, eq_comm]

lemma block_result (j : Fin 3) (X G G' : HalfSet m) (i : Fin m) :
    block (result j X G G') i = result j (block X i) (block G i) (block G' i) := by
  unfold result; split_ifs <;> simp only [block_union, block_sdiff, block_xorSet]

lemma eq_iff_block (U V : HalfSet m) : U = V ↔ ∀ i, block U i = block V i := by
  constructor
  · rintro rfl i; rfl
  · intro h; ext ⟨i, j⟩
    have := congrArg (j ∈ ·) (h i)
    simpa [block] using this

/-- A half-set is the same as its family of blocks. -/
def blocksEquiv (m : ℕ) : HalfSet m ≃ (Fin m → Finset (Fin m)) where
  toFun X i := block X i
  invFun B := univ.filter (fun p : Fin m × Fin m => p.2 ∈ B p.1)
  left_inv X := by ext ⟨i, j⟩; simp [block]
  right_inv B := by funext i; ext j; simp [block]

/-- Sums over half-sets of blockwise products factor as products of blockwise sums. -/
lemma sum_prod_block {R : Type} [CommSemiring R] (h : Fin m → Finset (Fin m) → R) :
    ∑ X : HalfSet m, ∏ i, h i (block X i) = ∏ i, ∑ S : Finset (Fin m), h i S := by
  rw [Fintype.prod_sum]
  exact Equiv.sum_comp (blocksEquiv m) (fun B => ∏ i, h i (B i))

/-- Number of selector pairs `(γ, γ')` with `result j X (selected γ) (selected γ') = U`. -/
noncomputable def gam (j : Fin 3) (X U : HalfSet m) : ℕ :=
  (univ.filter (fun q : Selector m × Selector m =>
    result j X (selected q.1) (selected q.2) = U)).card

lemma gam_eq_prod (j : Fin 3) (X U : HalfSet m) :
    gam j X U = ∏ i, blockGamma j (block X i) (block U i) := by
  classical
  unfold gam blockGamma
  rw [← Fintype.card_piFinset]
  refine Finset.card_bij' (fun q _ i => (q.1 i, q.2 i)) (fun f _ => (fun i => (f i).1, fun i => (f i).2))
    ?_ ?_ ?_ ?_
  · intro q hq
    simp only [mem_filter, mem_univ, true_and] at hq
    simp only [Fintype.mem_piFinset, mem_filter, mem_univ, true_and]
    intro i
    rw [← hq, block_result, block_selected, block_selected]
  · intro f hf
    simp only [Fintype.mem_piFinset, mem_filter, mem_univ, true_and] at hf
    simp only [mem_filter, mem_univ, true_and]
    rw [eq_iff_block]
    intro i
    rw [block_result, block_selected, block_selected]
    exact hf i
  · intro q _; rfl
  · intro f _; rfl

end Blocks

/-! ### Splitting the load -/

section Split
variable {m : ℕ}

/-- `L_j(U)`: triples with `X` a center for `Y` whose `j`-th alternative equals `U`. -/
noncomputable def Lj (φA φB : LabelMap m) (Y : HalfSet m) (j : Fin 3) (U : HalfSet m) : ℕ := by
  classical
  exact ∑ X : HalfSet m, if Center φA φB X Y then gam j X U else 0

lemma leadsTo_iff {ι : Type} [DecidableEq ι] (X G G' U : Cube ι) :
    LeadsTo X G G' U ↔ ∃ j : Fin 3, result j X G G' = U := by
  constructor
  · rintro (h | h | h)
    · exact ⟨0, by simp [result, h]⟩
    · exact ⟨1, by simp [result, h]⟩
    · exact ⟨2, by simp [result, h]⟩
  · rintro ⟨j, hj⟩
    fin_cases j
    · left; simp [result] at hj; exact hj.symm
    · right; left; simp [result] at hj; exact hj.symm
    · right; right; simp [result] at hj; exact hj.symm

open Classical in
lemma card_center_result (φA φB : LabelMap m) (Y U : HalfSet m) (j : Fin 3) :
    (univ.filter (fun p : HalfSet m × Selector m × Selector m =>
      Center φA φB p.1 Y ∧ result j p.1 (selected p.2.1) (selected p.2.2) = U)).card =
      Lj φA φB Y j U := by
  classical
  unfold Lj gam
  rw [Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun X _ => ?_
  by_cases hX : Center φA φB X Y
  · simp only [hX, true_and, if_true]; rw [Finset.card_filter]
  · simp [hX]

lemma loadY_le (φA φB : LabelMap m) (Y U : HalfSet m) :
    loadY φA φB Y U ≤ ∑ j : Fin 3, Lj φA φB Y j U := by
  classical
  unfold loadY
  simp_rw [← card_center_result]
  refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
  intro p hp
  simp only [mem_filter, mem_univ, true_and, leadsTo_iff] at hp
  obtain ⟨hc, j, hj⟩ := hp
  simp only [mem_biUnion, mem_univ, true_and, mem_filter]
  exact ⟨j, hc, hj⟩

lemma sq_sum_three_le (a : Fin 3 → ℝ) : (∑ j, a j) ^ 2 ≤ 3 * ∑ j, a j ^ 2 := by
  simp only [Fin.sum_univ_three]
  nlinarith [sq_nonneg (a 0 - a 1), sq_nonneg (a 1 - a 2), sq_nonneg (a 0 - a 2)]

lemma loadY_sq_le (φA φB : LabelMap m) (Y U : HalfSet m) :
    (loadY φA φB Y U : ℝ) ^ 2 ≤ 3 * ∑ j : Fin 3, (Lj φA φB Y j U : ℝ) ^ 2 := by
  refine le_trans ?_ (sq_sum_three_le _)
  have h : (loadY φA φB Y U : ℝ) ≤ ∑ j : Fin 3, (Lj φA φB Y j U : ℝ) := by
    exact_mod_cast loadY_le φA φB Y U
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) h 2

end Split

/-! ### Second moment of a single load -/

section Moment
variable {m : ℕ}

lemma center_iff (φA φB : LabelMap m) (X Y : HalfSet m) :
    Center φA φB X Y ↔ parity X = φB Y ∧ φA X = parity Y := by
  unfold Center alpha beta; exact Prod.mk.injEq _ _ _ _ ▸ Iff.rfl

lemma Lj_eq (φA φB : LabelMap m) (Y : HalfSet m) (j : Fin 3) (U : HalfSet m) :
    (Lj φA φB Y j U : ℝ) = ∑ X : HalfSet m,
      (if parity X = φB Y then (gam j X U : ℝ) else 0) *
        (if φA X = parity Y then (1 : ℝ) else 0) := by
  classical
  unfold Lj
  push_cast
  refine Finset.sum_congr rfl fun X _ => ?_
  by_cases h1 : parity X = φB Y <;> by_cases h2 : φA X = parity Y <;>
    simp [center_iff, h1, h2]

lemma card_bits : Fintype.card (Bits m) = 2 ^ m := by simp

lemma sum_gam (j : Fin 3) (π : Bits m) (U : HalfSet m) :
    ∑ X : HalfSet m, (if parity X = π then gam j X U else 0) =
      ∏ i, blockS j (π i) (block U i) := by
  unfold blockS
  rw [← sum_prod_block (fun i S => if decide (S.card % 2 = 1) = π i then
    blockGamma j S (block U i) else 0)]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [Finset.prod_ite_zero, gam_eq_prod]
  congr 1
  simp only [mem_univ, true_implies, parity, funext_iff]

lemma sum_gam_sq (j : Fin 3) (π : Bits m) (U : HalfSet m) :
    ∑ X : HalfSet m, (if parity X = π then gam j X U ^ 2 else 0) =
      ∏ i, blockT j (π i) (block U i) := by
  unfold blockT
  rw [← sum_prod_block (fun i S => if decide (S.card % 2 = 1) = π i then
    blockGamma j S (block U i) ^ 2 else 0)]
  refine Finset.sum_congr rfl fun X _ => ?_
  rw [Finset.prod_ite_zero, gam_eq_prod, ← Finset.prod_pow]
  congr 1
  simp only [mem_univ, true_implies, parity, funext_iff]

/-- Equation (3) of the paper, with the two sums over `X` already factored over blocks. -/
lemma mean_Lj_sq (φB : LabelMap m) (Y : HalfSet m) (j : Fin 3) (U : HalfSet m) :
    uniformMean (fun φA : LabelMap m => (Lj φA φB Y j U : ℝ) ^ 2) ≤
      1 / (2 : ℝ) ^ m * ∏ i, (blockT j (φB Y i) (block U i) : ℝ) +
      1 / ((2 : ℝ) ^ m) ^ 2 * (∏ i, (blockS j (φB Y i) (block U i) : ℝ)) ^ 2 := by
  classical
  simp_rw [Lj_eq]
  have key := uniformMean_sq_le (α := LabelMap m)
    (fun X => if parity X = φB Y then (gam j X U : ℝ) else 0)
    (fun X => by positivity)
    (fun X φA => if φA X = parity Y then (1 : ℝ) else 0)
    (1 / (2 : ℝ) ^ m) (1 / ((2 : ℝ) ^ m) ^ 2)
    (fun X X' => by
      have h := uniformMean_ind_mul (α := HalfSet m) (β := Bits m) X X' (parity Y) (parity Y)
      rw [card_bits] at h
      push_cast at h
      exact h)
  refine le_trans key (le_of_eq ?_)
  congr 2
  · have h := congrArg (fun n : ℕ => (n : ℝ)) (sum_gam_sq j (φB Y) U)
    push_cast at h
    rw [← h]
    refine Finset.sum_congr rfl fun X _ => ?_
    split_ifs <;> simp
  · have h := congrArg (fun n : ℕ => (n : ℝ)) (sum_gam j (φB Y) U)
    push_cast at h
    rw [← h]

end Moment

/-! ### Summing over `U` and the numerical bound -/

section Final
variable {m : ℕ}

lemma sum_mean_Lj_sq (φB : LabelMap m) (Y : HalfSet m) (j : Fin 3) :
    ∑ U : HalfSet m, uniformMean (fun φA : LabelMap m => (Lj φA φB Y j U : ℝ) ^ 2) ≤
      1 / (2 : ℝ) ^ m * ∏ i, ∑ S : Finset (Fin m), (blockT j (φB Y i) S : ℝ) +
      1 / ((2 : ℝ) ^ m) ^ 2 * ∏ i, ∑ S : Finset (Fin m), (blockS j (φB Y i) S : ℝ) ^ 2 := by
  refine le_trans (Finset.sum_le_sum fun U _ => mean_Lj_sq φB Y j U) (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 2
  · exact sum_prod_block (fun i S => (blockT j (φB Y i) S : ℝ))
  · simp_rw [← Finset.prod_pow]
    exact sum_prod_block (fun i S => (blockS j (φB Y i) S : ℝ) ^ 2)

lemma one_add_div_pow_le_exp (c : ℝ) (hc : 0 ≤ c) (hm : 0 < m) :
    (1 + c / m) ^ m ≤ Real.exp c := by
  have h1 : 1 + c / m ≤ Real.exp (c / m) := by
    have := Real.add_one_le_exp (c / m); linarith
  have h0 : 0 ≤ 1 + c / m := by positivity
  calc (1 + c / m) ^ m ≤ Real.exp (c / m) ^ m := pow_le_pow_left₀ h0 h1 m
    _ = Real.exp c := by
      rw [← Real.exp_nat_mul]; congr 1; field_simp

lemma exp_three_add_exp_one_le : Real.exp 3 + Real.exp 1 ≤ 25 := by
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h3]
  have : Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ h0.le h.le 3
  norm_num at this ⊢
  linarith

lemma two_pow_split (hm : 5 ≤ m) (k : ℕ) (hk : k ≤ 3) :
    (2 : ℝ) ^ ((m - k) * m) = 2 ^ (m ^ 2 - 4 * m) * ((2 : ℝ) ^ m) ^ (4 - k) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 5 := ⟨m - 5, by omega⟩
  have e1 : (n + 5) ^ 2 - 4 * (n + 5) = n ^ 2 + 6 * n + 5 := by
    apply Nat.sub_eq_of_eq_add; ring
  have e2 : (n + 5 - k) * (n + 5) = (n ^ 2 + 6 * n + 5) + (n + 5) * (4 - k) := by
    have e : n + 5 - k = n + (5 - k) := by omega
    rw [e]
    interval_cases k <;> norm_num <;> ring
  rw [e1, e2, pow_add, pow_mul]

lemma term_bound (hm : 5 ≤ m) (c : ℝ) (hc : 0 ≤ c) (k : ℕ) (hk : k ≤ 3) :
    1 / ((2 : ℝ) ^ m) ^ (4 - k) * ((1 + c / m) * (m : ℝ) ^ 4 * 2 ^ (m - k)) ^ m ≤
      Real.exp c * ((m : ℝ) ^ (4 * m) * 2 ^ (m ^ 2 - 4 * m)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have e : 1 / ((2 : ℝ) ^ m) ^ (4 - k) * ((1 + c / m) * (m : ℝ) ^ 4 * 2 ^ (m - k)) ^ m =
      (1 + c / m) ^ m * ((m : ℝ) ^ (4 * m) * 2 ^ (m ^ 2 - 4 * m)) := by
    rw [mul_pow, mul_pow, ← pow_mul (m : ℝ) 4 m, ← pow_mul (2 : ℝ) (m - k) m,
      two_pow_split hm k hk]
    have : ((2 : ℝ) ^ m) ^ (4 - k) ≠ 0 := by positivity
    field_simp
  rw [e]
  have hpos : 0 ≤ (m : ℝ) ^ (4 * m) * 2 ^ (m ^ 2 - 4 * m) := by positivity
  exact mul_le_mul_of_nonneg_right (one_add_div_pow_le_exp c hc (by omega)) hpos

lemma per_j_bound (hm : 5 ≤ m) (φB : LabelMap m) (Y : HalfSet m) (j : Fin 3) :
    ∑ U : HalfSet m, uniformMean (fun φA : LabelMap m => (Lj φA φB Y j U : ℝ) ^ 2) ≤
      25 * ((m : ℝ) ^ (4 * m) * 2 ^ (m ^ 2 - 4 * m)) := by
  refine le_trans (sum_mean_Lj_sq φB Y j) ?_
  have hS : ∀ i, ∑ S : Finset (Fin m), (blockS j (φB Y i) S : ℝ) ^ 2 =
      (1 + 1 / (m : ℝ)) * (m : ℝ) ^ 4 * 2 ^ (m - 2) :=
    fun i => (block_sums (by omega) (φB Y i) j).1
  have hT : ∀ i, ∑ S : Finset (Fin m), (blockT j (φB Y i) S : ℝ) ≤
      (1 + 3 / (m : ℝ)) * (m : ℝ) ^ 4 * 2 ^ (m - 3) :=
    fun i => (block_sums (by omega) (φB Y i) j).2
  have hT' : ∏ i, ∑ S : Finset (Fin m), (blockT j (φB Y i) S : ℝ) ≤
      ((1 + 3 / (m : ℝ)) * (m : ℝ) ^ 4 * 2 ^ (m - 3)) ^ m := by
    calc _ ≤ ∏ _i : Fin m, (1 + 3 / (m : ℝ)) * (m : ℝ) ^ 4 * 2 ^ (m - 3) :=
          Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hT i)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hS' : ∏ i, ∑ S : Finset (Fin m), (blockS j (φB Y i) S : ℝ) ^ 2 =
      ((1 + 1 / (m : ℝ)) * (m : ℝ) ^ 4 * 2 ^ (m - 2)) ^ m := by
    rw [Finset.prod_congr rfl fun i _ => hS i, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  rw [hS']
  have b1 := term_bound hm 3 (by norm_num) 3 le_rfl
  have b2 := term_bound hm 1 (by norm_num) 2 (by norm_num)
  simp only [show 4 - 3 = 1 by rfl, show 4 - 2 = 2 by rfl, pow_one] at b1 b2
  have hpos : 0 ≤ (m : ℝ) ^ (4 * m) * 2 ^ (m ^ 2 - 4 * m) := by positivity
  have hE := exp_three_add_exp_one_le
  have h2 : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ m := by positivity
  calc 1 / (2 : ℝ) ^ m * ∏ i, ∑ S : Finset (Fin m), (blockT j (φB Y i) S : ℝ) +
        1 / ((2 : ℝ) ^ m) ^ 2 * ((1 + 1 / (m : ℝ)) * (m : ℝ) ^ 4 * 2 ^ (m - 2)) ^ m
      ≤ 1 / (2 : ℝ) ^ m * ((1 + 3 / (m : ℝ)) * (m : ℝ) ^ 4 * 2 ^ (m - 3)) ^ m +
        1 / ((2 : ℝ) ^ m) ^ 2 * ((1 + 1 / (m : ℝ)) * (m : ℝ) ^ 4 * 2 ^ (m - 2)) ^ m := by
        gcongr
    _ ≤ Real.exp 3 * ((m : ℝ) ^ (4 * m) * 2 ^ (m ^ 2 - 4 * m)) +
        Real.exp 1 * ((m : ℝ) ^ (4 * m) * 2 ^ (m ^ 2 - 4 * m)) := add_le_add b1 b2
    _ ≤ 25 * ((m : ℝ) ^ (4 * m) * 2 ^ (m ^ 2 - 4 * m)) := by nlinarith

end Final

end BTHelper_load_second_moment

open BTHelper_load_second_moment in
theorem solution {m : ℕ} (hm : 5 ≤ m) (Y : HalfSet m) (φB : LabelMap m) :
    uniformMean (fun φA : LabelMap m => ∑ U : HalfSet m, (loadY φA φB Y U : ℝ)^2) ≤
      250 * (m : ℝ)^(4*m) * 2^(m^2-4*m) := by
  rw [uniformMean_sum]
  calc ∑ U : HalfSet m, uniformMean (fun φA : LabelMap m => (loadY φA φB Y U : ℝ) ^ 2)
      ≤ ∑ U : HalfSet m, uniformMean (fun φA : LabelMap m =>
          3 * ∑ j : Fin 3, (Lj φA φB Y j U : ℝ) ^ 2) :=
        Finset.sum_le_sum fun U _ => uniformMean_mono fun φA => loadY_sq_le φA φB Y U
    _ = 3 * ∑ j : Fin 3, ∑ U : HalfSet m,
          uniformMean (fun φA : LabelMap m => (Lj φA φB Y j U : ℝ) ^ 2) := by
        simp_rw [uniformMean_mul_left, uniformMean_sum, ← Finset.mul_sum]
        rw [Finset.sum_comm]
    _ ≤ 3 * ∑ _j : Fin 3, 25 * ((m : ℝ) ^ (4 * m) * 2 ^ (m ^ 2 - 4 * m)) := by
        gcongr with j _
        exact per_j_bound hm φB Y j
    _ ≤ 250 * (m : ℝ)^(4*m) * 2^(m^2-4*m) := by
        have hpos : 0 ≤ (m : ℝ) ^ (4 * m) * 2 ^ (m ^ 2 - 4 * m) := by positivity
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        nlinarith
