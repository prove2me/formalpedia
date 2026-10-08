-- Prove2me | solution 1 for ExtensionComplexity.TSP.rectangle_cover_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T22:57:34.424718+00:00
-- url     : https://prove2.me/submissions/35f517be-f80b-4510-a075-211637648070

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_ExtensionComplexity_TSP_Polytope
import Definitions.Def_ExtensionComplexity_TSP_SlackMatrix
import Definitions.Def_ExtensionComplexity_TSP_CorrelationMatrix
import Definitions.Def_ExtensionComplexity_TSP_CutCor
import Definitions.Def_ExtensionComplexity_TSP_TSPPolytope


open Matrix ExtensionComplexity.TSP Set

namespace XCT

section Lemma6

lemma bitVec_mul_self {n : ℕ} (b : Fin n → Bool) (i : Fin n) : bitVec b i * bitVec b i = bitVec b i := by
  unfold bitVec
  split_ifs <;> simp

lemma bitDot_cast {n : ℕ} (a b : Fin n → Bool) :
    (bitDot a b : ℝ) = ∑ i, bitVec a i * bitVec b i := by
  classical
  unfold bitDot
  rw [Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold bitVec
  cases a i <;> cases b i <;> simp

lemma corIneq_dot_outer {n : ℕ} (a b : Fin n → Bool) :
    corIneqCoeff a ⬝ᵥ outerBits b = 2 * (bitDot a b : ℝ) - (bitDot a b : ℝ) ^ 2 := by
  classical
  rw [bitDot_cast]
  simp only [dotProduct, corIneqCoeff, outerBits, Fintype.sum_prod_type, sub_mul,
    Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp only [if_true]
      rw [bitVec_mul_self]
      ring
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  · rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

lemma one_sub_corIneq {n : ℕ} (a b : Fin n → Bool) :
    1 - corIneqCoeff a ⬝ᵥ outerBits b = matM n a b := by
  rw [corIneq_dot_outer, matM]
  ring

lemma mem_corPolytope_iff {n : ℕ} (x : Fin n × Fin n → ℝ) :
    x ∈ corPolytope n ↔ ∃ w : (Fin n → Bool) → ℝ, (∀ b, 0 ≤ w b) ∧ ∑ b, w b = 1 ∧
      ∑ b, w b • outerBits b = x := by
  classical
  unfold corPolytope
  constructor
  · intro hx
    obtain ⟨ι, _, w', z', hw0, hw1, hz, hx⟩ := mem_convexHull_iff_exists_fintype.1 hx
    choose g hg using hz
    refine ⟨fun j => ∑ i ∈ Finset.univ.filter (fun i => g i = j), w' i, fun j =>
      Finset.sum_nonneg fun i _ => hw0 i, ?_, ?_⟩
    · rw [← hw1]
      exact Finset.sum_fiberwise Finset.univ g w'
    · rw [← hx]
      simp_rw [Finset.sum_smul]
      rw [← Finset.sum_fiberwise Finset.univ g (fun i => w' i • z' i)]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_filter] at hi
      rw [← hg i, hi.2]
  · rintro ⟨w, hw0, hw1, hx⟩
    exact mem_convexHull_of_exists_fintype w _ hw0 hw1 (fun j => mem_range_self j) hx

/-- **Lemma 6**. -/
theorem cor_valid_inequality_slack {n : ℕ} (a : Fin n → Bool) :
    (∀ x ∈ corPolytope n, corIneqCoeff a ⬝ᵥ x ≤ 1) ∧
      ∀ b : Fin n → Bool, 1 - corIneqCoeff a ⬝ᵥ outerBits b = matM n a b := by
  refine ⟨fun x hx => ?_, one_sub_corIneq a⟩
  obtain ⟨w, hw0, hw1, rfl⟩ := (mem_corPolytope_iff x).1 hx
  rw [dotProduct_sum]
  calc ∑ b, corIneqCoeff a ⬝ᵥ (w b • outerBits b) ≤ ∑ b, w b := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [dotProduct_smul, smul_eq_mul]
        have : corIneqCoeff a ⬝ᵥ outerBits b ≤ 1 := by
          have := one_sub_corIneq a b
          have h0 : 0 ≤ matM n a b := sq_nonneg _
          linarith
        nlinarith [hw0 b]
    _ = 1 := hw1

end Lemma6

section KW

open Classical in
/-- Number of disjoint pairs in a rectangle. -/
noncomputable def disj (n : ℕ) (A B : Set (Fin n → Bool)) : ℕ :=
  ∑ a, ∑ b, if a ∈ A ∧ b ∈ B ∧ bitDot a b = 0 then 1 else 0

lemma bitDot_cons {n : ℕ} (x y : Bool) (a b : Fin n → Bool) :
    bitDot (Fin.cons x a : Fin (n + 1) → Bool) (Fin.cons y b) =
      (if (x && y) then 1 else 0) + bitDot a b := by
  classical
  unfold bitDot
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp

lemma sum_cons {n : ℕ} {M : Type*} [AddCommMonoid M] (f : (Fin (n + 1) → Bool) → M) :
    ∑ a, f a = ∑ x : Bool, ∑ a : Fin n → Bool, f (Fin.cons x a) := by
  rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma kw_point {a0 a1 b0 b1 : Prop} [Decidable a0] [Decidable a1] [Decidable b0] [Decidable b1]
    (d : ℕ) (hc : a1 → b1 → 1 + d ≠ 1) :
    ((if a1 ∧ b1 ∧ 1 + d = 0 then 1 else 0) + (if a1 ∧ b0 ∧ d = 0 then 1 else 0)) +
        ((if a0 ∧ b1 ∧ d = 0 then 1 else 0) + (if a0 ∧ b0 ∧ d = 0 then 1 else 0)) ≤
      (if a0 ∧ (b0 ∨ b1) ∧ d = 0 then 1 else 0) + (if (a0 ∨ a1) ∧ b0 ∧ d = 0 then 1 else 0) := by
  have h1 : ¬ (1 + d = 0) := by omega
  by_cases hd : d = 0
  · subst hd
    have hc' : ¬ (a1 ∧ b1) := fun h => hc h.1 h.2 rfl
    by_cases a0 <;> by_cases a1 <;> by_cases b0 <;> by_cases b1 <;> simp_all
  · simp [hd]

/-- **Kaibel–Weltge**: a rectangle avoiding `aᵀb = 1` contains at most `2^n` disjoint pairs. -/
theorem disj_le (n : ℕ) : ∀ A B : Set (Fin n → Bool),
    (∀ a ∈ A, ∀ b ∈ B, bitDot a b ≠ 1) → disj n A B ≤ 2 ^ n := by
  classical
  induction n with
  | zero =>
    intro A B _
    unfold disj
    calc _ ≤ ∑ _a : Fin 0 → Bool, ∑ _b : Fin 0 → Bool, 1 :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => by split_ifs <;> simp
      _ = 1 := by simp
      _ = 2 ^ 0 := rfl
  | succ n ih =>
    intro A B hAB
    let A0 : Set (Fin n → Bool) := {a | (Fin.cons false a : Fin (n + 1) → Bool) ∈ A}
    let A1 : Set (Fin n → Bool) := {a | (Fin.cons true a : Fin (n + 1) → Bool) ∈ A}
    let B0 : Set (Fin n → Bool) := {b | (Fin.cons false b : Fin (n + 1) → Bool) ∈ B}
    let B1 : Set (Fin n → Bool) := {b | (Fin.cons true b : Fin (n + 1) → Bool) ∈ B}
    have h1 : disj n A0 (B0 ∪ B1) ≤ 2 ^ n := by
      refine ih _ _ fun a ha b hb => ?_
      rcases hb with hb | hb
      · have := hAB _ ha _ hb
        simpa [bitDot_cons] using this
      · have := hAB _ ha _ hb
        simpa [bitDot_cons] using this
    have h2 : disj n (A0 ∪ A1) B0 ≤ 2 ^ n := by
      refine ih _ _ fun a ha b hb => ?_
      rcases ha with ha | ha
      · have := hAB _ ha _ hb
        simpa [bitDot_cons] using this
      · have := hAB _ ha _ hb
        simpa [bitDot_cons] using this
    have key : disj (n + 1) A B ≤ disj n A0 (B0 ∪ B1) + disj n (A0 ∪ A1) B0 := by
      unfold disj
      simp only [sum_cons (n := n), Fintype.sum_bool]
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
      have hc := hAB (Fin.cons true a) (b := Fin.cons true b)
      simp only [bitDot_cons, Bool.and_self, Bool.and_false, Bool.false_and, if_true,
        Bool.false_eq_true, if_false, zero_add] at hc ⊢
      simp only [mem_union, A0, A1, B0, B1, Set.mem_ofPred_eq]
      exact kw_point _ hc
    calc disj (n + 1) A B ≤ disj n A0 (B0 ∪ B1) + disj n (A0 ∪ A1) B0 := key
      _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add h1 h2
      _ = 2 ^ (n + 1) := by ring

/-- There are `3^n` disjoint pairs. -/
theorem card_disjoint_pairs (n : ℕ) :
    ∑ a : Fin n → Bool, ∑ b : Fin n → Bool, (if bitDot a b = 0 then 1 else 0 : ℕ) = 3 ^ n := by
  induction n with
  | zero => simp [bitDot]
  | succ n ih =>
    simp only [sum_cons (n := n), Fintype.sum_bool]
    simp only [bitDot_cons, Bool.and_self, Bool.and_false, Bool.false_and, if_true,
      Bool.false_eq_true, if_false, zero_add]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, false_and, if_false, Finset.sum_const_zero,
      zero_add]
    have : ∀ x : Fin n → Bool, (∑ y : Fin n → Bool, if bitDot x y = 0 then 1 else 0) +
        (∑ y : Fin n → Bool, if bitDot x y = 0 then 1 else 0) +
        (∑ y : Fin n → Bool, if bitDot x y = 0 then 1 else 0) =
        3 * ∑ y : Fin n → Bool, if bitDot x y = 0 then 1 else 0 := fun x => by ring
    simp only [Finset.sum_add_distrib, ih] at *
    ring

lemma suppM_iff {n : ℕ} (a b : Fin n → Bool) : suppM n a b ↔ bitDot a b ≠ 1 := by
  unfold suppM matM
  rw [ne_eq, pow_eq_zero_iff two_ne_zero, sub_eq_zero, not_iff_not]
  constructor
  · intro h
    exact_mod_cast h.symm
  · intro h
    rw [h]
    simp

/-- The counting core of Theorem 1: `3^n ≤ k 2^n`. -/
theorem cover_count {n k : ℕ} (R : Fin k → Set (Fin n → Bool) × Set (Fin n → Bool))
    (hR : IsOneRectangleCover (suppM n) R) : 3 ^ n ≤ k * 2 ^ n := by
  classical
  obtain ⟨hR1, hR2⟩ := hR
  rw [← card_disjoint_pairs]
  calc ∑ a : Fin n → Bool, ∑ b : Fin n → Bool, (if bitDot a b = 0 then 1 else 0 : ℕ)
      ≤ ∑ a, ∑ b, ∑ l : Fin k,
          (if a ∈ (R l).1 ∧ b ∈ (R l).2 ∧ bitDot a b = 0 then 1 else 0 : ℕ) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        split_ifs with h
        · obtain ⟨l, hl1, hl2⟩ := hR2 a b ((suppM_iff a b).2 (by rw [h]; exact zero_ne_one))
          exact le_trans (by simp [hl1, hl2, h]) (Finset.single_le_sum (f := fun l =>
            (if a ∈ (R l).1 ∧ b ∈ (R l).2 ∧ bitDot a b = 0 then 1 else 0 : ℕ))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ l))
        · exact Nat.zero_le _
    _ = ∑ l : Fin k, disj n (R l).1 (R l).2 := by
        unfold disj
        rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
    _ ≤ ∑ _l : Fin k, 2 ^ n := Finset.sum_le_sum fun l _ =>
        disj_le n _ _ fun a ha b hb => (suppM_iff a b).1 (hR1 l a ha b hb)
    _ = k * 2 ^ n := by simp

lemma two_rpow_logb (n : ℕ) : (2 : ℝ) ^ (Real.logb 2 (3 / 2) * n) = (3 / 2 : ℝ) ^ n := by
  rw [Real.rpow_mul (x := (2 : ℝ)) (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num),
    Real.rpow_natCast]

lemma logb_pos' : 0 < Real.logb 2 (3 / 2 : ℝ) := Real.logb_pos (by norm_num) (by norm_num)

/-- **Theorem 1**. -/
theorem rectangle_cover_lower_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ (k : ℕ)
      (R : Fin k → Set (Fin n → Bool) × Set (Fin n → Bool)),
      IsOneRectangleCover (suppM n) R → (2 : ℝ) ^ (C * n) ≤ k := by
  refine ⟨Real.logb 2 (3 / 2), logb_pos', 0, fun n _ k R hR => ?_⟩
  rw [two_rpow_logb]
  have h := cover_count R hR
  have h' : (3 : ℝ) ^ n ≤ k * 2 ^ n := by exact_mod_cast h
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_pow, div_le_iff₀ h2]
  exact h'

end KW

end XCT

open Matrix ExtensionComplexity.TSP

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ (k : ℕ)
      (R : Fin k → Set (Fin n → Bool) × Set (Fin n → Bool)),
      IsOneRectangleCover (suppM n) R → (2 : ℝ) ^ (C * n) ≤ k :=
  XCT.rectangle_cover_lower_bound
