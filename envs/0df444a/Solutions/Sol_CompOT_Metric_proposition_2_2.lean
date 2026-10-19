-- Prove2me | solution 1 for CompOT.Metric.proposition_2_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-17T00:40:29.157665+00:00
-- url     : https://prove2.me/submissions/2a73a023-6b4d-4e27-be29-0899312fd294

-- Licensed under Apache 2.0. Full exact theorem: finite p-Wasserstein is a metric.
import Mathlib
import Definitions.Def_CompOT_Metric_Defs


open scoped BigOperators
open CompOT.Assignment

namespace OTMetricProof

lemma coupling_entry_le_row {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    {P : Matrix (Fin n) (Fin m) ℝ} (hP : P ∈ couplings a b) (i : Fin n) (j : Fin m) :
    P i j ≤ a i := by
  rw [← hP.2.1 i]
  exact Finset.single_le_sum (fun k _ => hP.1 i k) (Finset.mem_univ j)

lemma coupling_entry_le_col {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    {P : Matrix (Fin n) (Fin m) ℝ} (hP : P ∈ couplings a b) (i : Fin n) (j : Fin m) :
    P i j ≤ b j := by
  rw [← hP.2.2 j]
  exact Finset.single_le_sum (fun k _ => hP.1 k j) (Finset.mem_univ i)

lemma product_coupling {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m)) :
    (fun i j => a i * b j) ∈ couplings a b := by
  refine ⟨fun i j => mul_nonneg (ha.1 i) (hb.1 j), ?_, ?_⟩
  · intro i
    simp only [← Finset.mul_sum, hb.2, mul_one]
  · intro j
    simp only [← Finset.sum_mul, ha.2, one_mul]

lemma coupling_nonempty {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m)) :
    (couplings a b).Nonempty := ⟨_, product_coupling ha hb⟩

lemma coupling_transpose {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    {P : Matrix (Fin n) (Fin m) ℝ} (hP : P ∈ couplings a b) :
    P.transpose ∈ couplings b a :=
  ⟨fun i j => hP.1 j i, hP.2.2, hP.2.1⟩

lemma coupling_isClosed {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ) :
    IsClosed (couplings a b) := by
  change IsClosed {P : Matrix (Fin n) (Fin m) ℝ | (∀ i j, 0 ≤ P i j) ∧
    (∀ i, ∑ j, P i j = a i) ∧ (∀ j, ∑ i, P i j = b j)}
  have h₁ : IsClosed {P : Matrix (Fin n) (Fin m) ℝ | ∀ i j, 0 ≤ P i j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le (continuous_const (y := (0 : ℝ)))
        (show Continuous (fun P : Matrix (Fin n) (Fin m) ℝ => P i j) by fun_prop)
  have h₂ : IsClosed {P : Matrix (Fin n) (Fin m) ℝ | ∀ i, ∑ j, P i j = a i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_eq
      (show Continuous (fun P : Matrix (Fin n) (Fin m) ℝ => ∑ j, P i j) by fun_prop)
      continuous_const
  have h₃ : IsClosed {P : Matrix (Fin n) (Fin m) ℝ | ∀ j, ∑ i, P i j = b j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_eq
      (show Continuous (fun P : Matrix (Fin n) (Fin m) ℝ => ∑ i, P i j) by fun_prop)
      continuous_const
  exact h₁.inter (h₂.inter h₃)

lemma coupling_isCompact {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (_hb : b ∈ stdSimplex ℝ (Fin m)) :
    IsCompact (couplings a b) := by
  have hbox : IsCompact (Set.Icc (0 : Fin n → Fin m → ℝ)
      (fun _ _ => (1 : ℝ))) := isCompact_Icc
  refine hbox.of_isClosed_subset (coupling_isClosed a b) ?_
  intro P hP
  show P ∈ Set.Icc (0 : Fin n → Fin m → ℝ) (fun _ _ => 1)
  exact ⟨hP.1, fun i j => (coupling_entry_le_row hP i j).trans
    (mem_Icc_of_mem_stdSimplex ha i).2⟩

end OTMetricProof


open scoped BigOperators
open CompOT.Assignment

namespace OTMetricProof

lemma continuous_frob {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) :
    Continuous (frob C) := by
  unfold frob
  fun_prop

lemma exists_optimal {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m)) :
    ∃ P, IsOptimalCoupling C a b P := by
  obtain ⟨P, hP, hmin⟩ := (coupling_isCompact ha hb).exists_isMinOn
    (coupling_nonempty ha hb) (continuous_frob C).continuousOn
  exact ⟨P, hP, fun Q hQ => hmin hQ⟩

lemma otCost_eq_of_optimal {n m : ℕ} {C : Matrix (Fin n) (Fin m) ℝ}
    {a : Fin n → ℝ} {b : Fin m → ℝ} {P : Matrix (Fin n) (Fin m) ℝ}
    (hP : IsOptimalCoupling C a b P) : CompOT.Metric.otCost C a b = frob C P := by
  let : Nonempty (couplings a b) := ⟨⟨P, hP.1⟩⟩
  have hb : BddBelow (Set.range (fun Q : couplings a b => frob C Q.1)) := by
    refine ⟨frob C P, ?_⟩
    rintro _ ⟨Q, rfl⟩
    exact hP.2 Q.1 Q.2
  exact le_antisymm (ciInf_le hb ⟨P, hP.1⟩) (le_ciInf fun Q => hP.2 Q.1 Q.2)

lemma exists_attained {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m)) :
    ∃ P ∈ couplings a b, CompOT.Metric.otCost C a b = frob C P := by
  obtain ⟨P, hP⟩ := exists_optimal C ha hb
  exact ⟨P, hP.1, otCost_eq_of_optimal hP⟩

lemma otCost_le {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    {P : Matrix (Fin n) (Fin m) ℝ} (hP : P ∈ couplings a b) :
    CompOT.Metric.otCost C a b ≤ frob C P := by
  obtain ⟨Q, hQ⟩ := exists_optimal C ha hb
  rw [otCost_eq_of_optimal hQ]
  exact hQ.2 P hP

lemma frob_nonneg {n m : ℕ} {C P : Matrix (Fin n) (Fin m) ℝ}
    (hC : ∀ i j, 0 ≤ C i j) (hP : ∀ i j, 0 ≤ P i j) : 0 ≤ frob C P := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (hC i j) (hP i j)

lemma otCost_nonneg {n m : ℕ} {C : Matrix (Fin n) (Fin m) ℝ}
    {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (hC : ∀ i j, 0 ≤ C i j) : 0 ≤ CompOT.Metric.otCost C a b := by
  obtain ⟨P, hP, he⟩ := exists_attained C ha hb
  rw [he]
  exact frob_nonneg hC hP.1

end OTMetricProof


open scoped BigOperators
open CompOT.Assignment CompOT.Metric

namespace OTMetricProof

lemma powCost_nonneg {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : ∀ i j, 0 ≤ D i j) (p : ℝ) : ∀ i j, 0 ≤ powCost D p i j :=
  fun i j => Real.rpow_nonneg (hD i j) p

lemma W_nonneg {n : ℕ} {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : ∀ i j, 0 ≤ D i j) (p : ℝ) {a b : Fin n → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin n)) :
    0 ≤ W D p a b :=
  Real.rpow_nonneg (otCost_nonneg ha hb (powCost_nonneg hD p)) _

lemma frob_transpose {n : ℕ} (C P : Matrix (Fin n) (Fin n) ℝ)
    (hC : ∀ i j, C i j = C j i) : frob C P.transpose = frob C P := by
  unfold frob
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hC j i]

lemma cost_symm {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : ∀ i j, C i j = C j i) {a b : Fin n → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin n)) :
    CompOT.Metric.otCost C a b = CompOT.Metric.otCost C b a := by
  obtain ⟨P, hP, heP⟩ := exists_attained C ha hb
  obtain ⟨Q, hQ, heQ⟩ := exists_attained C hb ha
  apply le_antisymm
  · calc
      CompOT.Metric.otCost C a b ≤ frob C Q.transpose := otCost_le C ha hb (coupling_transpose hQ)
      _ = CompOT.Metric.otCost C b a := (frob_transpose C Q hC).trans heQ.symm
  · calc
      CompOT.Metric.otCost C b a ≤ frob C P.transpose := otCost_le C hb ha (coupling_transpose hP)
      _ = CompOT.Metric.otCost C a b := (frob_transpose C P hC).trans heP.symm

lemma W_symm {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (p : ℝ)
    (hD : ∀ i j, D i j = D j i) {a b : Fin n → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin n)) :
    W D p a b = W D p b a := by
  unfold W
  rw [cost_symm (powCost D p) (fun i j => congrArg (fun x : ℝ => x ^ p) (hD i j)) ha hb]

lemma diagonal_coupling {n : ℕ} {a : Fin n → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) : Matrix.diagonal a ∈ couplings a a := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    simp only [Matrix.diagonal_apply]
    split_ifs
    · exact ha.1 i
    · exact le_refl 0
  · intro i
    change (∑ j : Fin n, if i = j then a i else 0) = a i
    simp
  · intro j
    change (∑ i : Fin n, if i = j then a i else 0) = a j
    simp

lemma frob_diagonal_zero {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : ∀ i, C i i = 0) (a : Fin n → ℝ) : frob C (Matrix.diagonal a) = 0 := by
  unfold frob
  simp [Matrix.diagonal_apply, hC]

lemma W_self {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) {p : ℝ} (hp : 1 ≤ p)
    (hD : ∀ i j, 0 ≤ D i j) (hz : ∀ i, D i i = 0) {a : Fin n → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) : W D p a a = 0 := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hd : frob (powCost D p) (Matrix.diagonal a) = 0 :=
    frob_diagonal_zero _ (fun i => by simp only [powCost, hz i, Real.zero_rpow hp0.ne']) a
  have hc : CompOT.Metric.otCost (powCost D p) a a = 0 :=
    le_antisymm ((otCost_le _ ha ha (diagonal_coupling ha)).trans_eq hd)
      (otCost_nonneg ha ha (powCost_nonneg hD p))
  simp only [W, hc, Real.zero_rpow (one_div_pos.mpr hp0).ne']

lemma W_eq_zero_imp_eq {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) {p : ℝ} (hp : 1 ≤ p)
    (hD : ∀ i j, 0 ≤ D i j) (hz : ∀ i j, D i j = 0 ↔ i = j) {a b : Fin n → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin n))
    (hw : W D p a b = 0) : a = b := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hc : CompOT.Metric.otCost (powCost D p) a b = 0 :=
    (Real.rpow_eq_zero (otCost_nonneg ha hb (powCost_nonneg hD p))
      (one_div_pos.mpr hp0).ne').mp hw
  obtain ⟨P, hP, heP⟩ := exists_attained (powCost D p) ha hb
  have hsum : frob (powCost D p) P = 0 := heP.symm.trans hc
  have hoff : ∀ i j, i ≠ j → P i j = 0 := by
    intro i j hij
    have hterm : powCost D p i j * P i j = 0 := by
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
        Finset.sum_nonneg fun l _ => mul_nonneg (powCost_nonneg hD p k l) (hP.1 k l))).mp hsum i (Finset.mem_univ i)
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun l _ =>
        mul_nonneg (powCost_nonneg hD p i l) (hP.1 i l))).mp hi j (Finset.mem_univ j)
    have hdpos : 0 < D i j := lt_of_le_of_ne (hD i j) (fun h => hij ((hz i j).mp h.symm))
    exact (mul_eq_zero.mp hterm).resolve_left (Real.rpow_pos_of_pos hdpos p).ne'
  funext i
  have hr : (∑ j, P i j) = P i i := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      exact hoff i j (Ne.symm hji)
    · simp
  have hc' : (∑ j, P j i) = P i i := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      exact hoff j i hji
    · simp
  exact (hP.2.1 i).symm.trans (hr.trans (hc'.symm.trans (hP.2.2 i)))

end OTMetricProof


noncomputable section
open Finset Matrix
open CompOT.Assignment CompOT.Metric
namespace OTMetricProof

variable {n : ℕ}

def glueWeight (b : Fin n → ℝ) (P Q : Matrix (Fin n) (Fin n) ℝ)
    (i j k : Fin n) : ℝ := P i j * Q j k / btilde b j

theorem btilde_pos (b : Fin n → ℝ) (j : Fin n) : 0 < btilde b j := by
  unfold btilde
  split_ifs with h
  · exact h
  · norm_num

theorem coupling_entry_zero_of_col_zero {a b : Fin n → ℝ}
    {P : Matrix (Fin n) (Fin n) ℝ} (hP : P ∈ couplings a b)
    {j : Fin n} (hj : b j = 0) (i : Fin n) : P i j = 0 := by
  have hle : P i j ≤ ∑ l, P l j := single_le_sum (fun l _ => hP.1 l j) (mem_univ i)
  rw [hP.2.2 j, hj] at hle
  exact le_antisymm hle (hP.1 i j)

theorem coupling_entry_zero_of_row_zero {a b : Fin n → ℝ}
    {P : Matrix (Fin n) (Fin n) ℝ} (hP : P ∈ couplings a b)
    {i : Fin n} (hi : a i = 0) (j : Fin n) : P i j = 0 := by
  have hle : P i j ≤ ∑ l, P i l := single_le_sum (fun l _ => hP.1 i l) (mem_univ j)
  rw [hP.2.1 i, hi] at hle
  exact le_antisymm hle (hP.1 i j)

theorem glueWeight_nonneg {a b c : Fin n → ℝ}
    {P Q : Matrix (Fin n) (Fin n) ℝ} (hP : P ∈ couplings a b) (hQ : Q ∈ couplings b c)
    (i j k : Fin n) : 0 ≤ glueWeight b P Q i j k :=
  div_nonneg (mul_nonneg (hP.1 i j) (hQ.1 j k)) (btilde_pos b j).le

theorem glueWeight_sum_right {a b c : Fin n → ℝ}
    {P Q : Matrix (Fin n) (Fin n) ℝ} (hb : ∀ j, 0 ≤ b j)
    (hP : P ∈ couplings a b) (hQ : Q ∈ couplings b c) (i j : Fin n) :
    ∑ k, glueWeight b P Q i j k = P i j := by
  simp only [glueWeight]
  rw [← sum_div, ← mul_sum, hQ.2.1 j]
  by_cases hj : 0 < b j
  · simp [btilde, hj, hj.ne']
  · have hz : b j = 0 := le_antisymm (le_of_not_gt hj) (hb j)
    rw [coupling_entry_zero_of_col_zero hP hz i]
    simp

theorem glueWeight_sum_left {a b c : Fin n → ℝ}
    {P Q : Matrix (Fin n) (Fin n) ℝ} (hb : ∀ j, 0 ≤ b j)
    (hP : P ∈ couplings a b) (hQ : Q ∈ couplings b c) (j k : Fin n) :
    ∑ i, glueWeight b P Q i j k = Q j k := by
  simp only [glueWeight]
  rw [← sum_div, ← sum_mul, hP.2.2 j]
  by_cases hj : 0 < b j
  · simp [btilde, hj, hj.ne', mul_div_cancel_left₀]
  · have hz : b j = 0 := le_antisymm (le_of_not_gt hj) (hb j)
    rw [coupling_entry_zero_of_row_zero hQ hz k]
    simp

theorem glue_apply (b : Fin n → ℝ) (P Q : Matrix (Fin n) (Fin n) ℝ) (i k : Fin n) :
    glue b P Q i k = ∑ j, glueWeight b P Q i j k := by
  unfold glue
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, glueWeight]
  apply sum_congr rfl
  intro j _
  ring

end OTMetricProof


noncomputable section
open Finset Matrix
open CompOT.Assignment CompOT.Metric
namespace OTMetricProof

variable {n : ℕ} {a b c : Fin n → ℝ}
variable {P Q : Matrix (Fin n) (Fin n) ℝ}

theorem glue_mem (hb : ∀ j, 0 ≤ b j)
    (hP : P ∈ couplings a b) (hQ : Q ∈ couplings b c) :
    glue b P Q ∈ couplings a c := by
  refine ⟨?_, ?_, ?_⟩
  · intro i k
    rw [glue_apply]
    exact sum_nonneg fun j _ => glueWeight_nonneg hP hQ i j k
  · intro i
    simp only [glue_apply]
    rw [sum_comm]
    simp only [glueWeight_sum_right hb hP hQ]
    exact hP.2.1 i
  · intro k
    simp only [glue_apply]
    rw [sum_comm]
    simp only [glueWeight_sum_left hb hP hQ]
    exact hQ.2.2 k

theorem glueWeight_cost_right (hb : ∀ j, 0 ≤ b j)
    (hP : P ∈ couplings a b) (hQ : Q ∈ couplings b c)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, ∑ k, glueWeight b P Q i j k * A i j) = frob A P := by
  unfold frob
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  rw [← sum_mul, glueWeight_sum_right hb hP hQ]
  exact mul_comm _ _

theorem glueWeight_cost_left (hb : ∀ j, 0 ≤ b j)
    (hP : P ∈ couplings a b) (hQ : Q ∈ couplings b c)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, ∑ k, glueWeight b P Q i j k * B j k) = frob B Q := by
  rw [sum_comm]
  unfold frob
  apply sum_congr rfl
  intro j _
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  rw [← sum_mul, glueWeight_sum_left hb hP hQ]
  exact mul_comm _ _

theorem glueWeight_cost_outer (b : Fin n → ℝ)
    (P Q C : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, ∑ k, glueWeight b P Q i j k * C i k) = frob C (glue b P Q) := by
  unfold frob
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro k _
  rw [← sum_mul, glue_apply]
  exact mul_comm _ _

end OTMetricProof


noncomputable section
open Finset
namespace OTMetricProof

theorem weighted_rpow {w x p : ℝ} (hw : 0 ≤ w) (hx : 0 ≤ x) (hp : p ≠ 0) :
    (w ^ (1 / p) * x) ^ p = w * x ^ p := by
  rw [Real.mul_rpow (Real.rpow_nonneg hw _) hx, ← Real.rpow_mul hw]
  rw [one_div_mul_cancel hp, Real.rpow_one]

theorem weighted_minkowski {ι : Type*} [Fintype ι]
    (w x y : ι → ℝ) {p : ℝ} (hp : 1 ≤ p)
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    (∑ i, w i * (x i + y i) ^ p) ^ (1 / p) ≤
      (∑ i, w i * x i ^ p) ^ (1 / p) + (∑ i, w i * y i ^ p) ^ (1 / p) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have h := Real.Lp_add_le_of_nonneg (s := univ)
    (f := fun i => w i ^ (1 / p) * x i)
    (g := fun i => w i ^ (1 / p) * y i) hp
    (fun i _ => mul_nonneg (Real.rpow_nonneg (hw i) _) (hx i))
    (fun i _ => mul_nonneg (Real.rpow_nonneg (hw i) _) (hy i))
  simp only [← mul_add, weighted_rpow (hw _) (hx _) hp0,
    weighted_rpow (hw _) (hy _) hp0,
    weighted_rpow (hw _) (add_nonneg (hx _) (hy _)) hp0] at h
  exact h

end OTMetricProof


noncomputable section
open Finset Matrix
open CompOT.Assignment CompOT.Metric
namespace OTMetricProof

variable {n : ℕ}

theorem glue_cost_triangle (D : Matrix (Fin n) (Fin n) ℝ) {p : ℝ} (hp : 1 ≤ p)
    (hD : ∀ i j, 0 ≤ D i j)
    (htri : ∀ i j k, D i k ≤ D i j + D j k)
    {a b c : Fin n → ℝ} {P Q : Matrix (Fin n) (Fin n) ℝ}
    (hb : ∀ j, 0 ≤ b j) (hP : P ∈ couplings a b) (hQ : Q ∈ couplings b c) :
    (frob (powCost D p) (glue b P Q)) ^ (1 / p) ≤
      (frob (powCost D p) P) ^ (1 / p) +
      (frob (powCost D p) Q) ^ (1 / p) := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hw : ∀ i j k, 0 ≤ glueWeight b P Q i j k := glueWeight_nonneg hP hQ
  have hm := weighted_minkowski
    (fun t : Fin n × (Fin n × Fin n) => glueWeight b P Q t.1 t.2.1 t.2.2)
    (fun t => D t.1 t.2.1) (fun t => D t.2.1 t.2.2) hp
    (fun t => hw _ _ _) (fun t => hD _ _) (fun t => hD _ _)
  simp only [Fintype.sum_prod_type] at hm
  have hc : (∑ i, ∑ j, ∑ k, glueWeight b P Q i j k * D i k ^ p) ≤
      ∑ i, ∑ j, ∑ k, glueWeight b P Q i j k * (D i j + D j k) ^ p := by
    apply sum_le_sum
    intro i _
    apply sum_le_sum
    intro j _
    apply sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hD i k) (htri i j k) hp0)
      (hw i j k)
  have hn : 0 ≤ ∑ i, ∑ j, ∑ k, glueWeight b P Q i j k * D i k ^ p := by
    exact sum_nonneg fun i _ => sum_nonneg fun j _ => sum_nonneg fun k _ =>
      mul_nonneg (hw i j k) (Real.rpow_nonneg (hD i k) p)
  have h := (Real.rpow_le_rpow hn hc (div_nonneg zero_le_one hp0)).trans hm
  change (∑ i, ∑ j, ∑ k, glueWeight b P Q i j k * powCost D p i k) ^ (1 / p) ≤
    (∑ i, ∑ j, ∑ k, glueWeight b P Q i j k * powCost D p i j) ^ (1 / p) +
    (∑ i, ∑ j, ∑ k, glueWeight b P Q i j k * powCost D p j k) ^ (1 / p) at h
  rw [glueWeight_cost_outer, glueWeight_cost_right hb hP hQ,
    glueWeight_cost_left hb hP hQ] at h
  exact h

end OTMetricProof


open CompOT.Assignment CompOT.Metric

namespace OTMetricProof

lemma W_triangle {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) {p : ℝ} (hp : 1 ≤ p)
    (hD : ∀ i j, 0 ≤ D i j) (htri : ∀ i j k, D i k ≤ D i j + D j k)
    {a b c : Fin n → ℝ} (ha : a ∈ stdSimplex ℝ (Fin n))
    (hb : b ∈ stdSimplex ℝ (Fin n)) (hc : c ∈ stdSimplex ℝ (Fin n)) :
    W D p a c ≤ W D p a b + W D p b c := by
  obtain ⟨P, hP, heP⟩ := exists_attained (powCost D p) ha hb
  obtain ⟨Q, hQ, heQ⟩ := exists_attained (powCost D p) hb hc
  have hbound := otCost_le (powCost D p) ha hc (glue_mem hb.1 hP hQ)
  have hroot := Real.rpow_le_rpow (otCost_nonneg ha hc (powCost_nonneg hD p))
    hbound (one_div_nonneg.mpr (le_trans zero_le_one hp))
  have h := hroot.trans (glue_cost_triangle D hp hD htri hb.1 hP hQ)
  simpa only [W, heP, heQ] using h

theorem native_metric {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (p : ℝ) (hp : 1 ≤ p)
    (hD_nonneg : ∀ i j, 0 ≤ D i j) (hD_symm : ∀ i j, D i j = D j i)
    (hD_zero : ∀ i j, D i j = 0 ↔ i = j)
    (hD_tri : ∀ i j k, D i k ≤ D i j + D j k) :
    ∀ a ∈ stdSimplex ℝ (Fin n), ∀ b ∈ stdSimplex ℝ (Fin n), ∀ c ∈ stdSimplex ℝ (Fin n),
      W D p a b = W D p b a ∧ 0 ≤ W D p a b ∧ (W D p a b = 0 ↔ a = b) ∧
      W D p a c ≤ W D p a b + W D p b c := by
  intro a ha b hb c hc
  refine ⟨W_symm D p hD_symm ha hb, W_nonneg hD_nonneg p ha hb, ?_,
    W_triangle D hp hD_nonneg hD_tri ha hb hc⟩
  constructor
  · exact W_eq_zero_imp_eq D hp hD_nonneg hD_zero ha hb
  · intro hab
    subst b
    exact W_self D hp hD_nonneg (fun i => (hD_zero i i).mpr rfl) ha

end OTMetricProof


namespace CompOT.Metric

open Matrix

/-- **Proposition 2.2** (p. 377). Let `D ∈ ℝ₊^{n×n}` be a distance on `⟦n⟧` (symmetric,
`D_{i,j} = 0 ↔ i = j`, triangle inequality) and `p ≥ 1`. Then `W_p(a, b) = L_{D^p}(a, b)^{1/p}`
(2.17) is a distance on `Σ_n`: symmetric, nonnegative, `W_p(a, b) = 0 ↔ a = b`, and it satisfies
the triangle inequality. -/
theorem proposition_2_2 {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (p : ℝ) (hp : 1 ≤ p)
    (hD_nonneg : ∀ i j, 0 ≤ D i j)
    (hD_symm : ∀ i j, D i j = D j i)
    (hD_zero : ∀ i j, D i j = 0 ↔ i = j)
    (hD_tri : ∀ i j k, D i k ≤ D i j + D j k) :
    ∀ a ∈ stdSimplex ℝ (Fin n), ∀ b ∈ stdSimplex ℝ (Fin n), ∀ c ∈ stdSimplex ℝ (Fin n),
      W D p a b = W D p b a ∧
      0 ≤ W D p a b ∧
      (W D p a b = 0 ↔ a = b) ∧
      W D p a c ≤ W D p a b + W D p b c := by
  exact OTMetricProof.native_metric D p hp hD_nonneg hD_symm hD_zero hD_tri

end CompOT.Metric

open CompOT.Metric

theorem solution {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (p : ℝ) (hp : 1 ≤ p)
    (hD_nonneg : ∀ i j, 0 ≤ D i j)
    (hD_symm : ∀ i j, D i j = D j i)
    (hD_zero : ∀ i j, D i j = 0 ↔ i = j)
    (hD_tri : ∀ i j k, D i k ≤ D i j + D j k) :
    ∀ a ∈ stdSimplex ℝ (Fin n), ∀ b ∈ stdSimplex ℝ (Fin n), ∀ c ∈ stdSimplex ℝ (Fin n),
      W D p a b = W D p b a ∧
      0 ≤ W D p a b ∧
      (W D p a b = 0 ↔ a = b) ∧
      W D p a c ≤ W D p a b + W D p b c := CompOT.Metric.proposition_2_2 D p hp hD_nonneg hD_symm hD_zero hD_tri
