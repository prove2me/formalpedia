-- Prove2me | solution 1 for ChoiceRM.MNL.theorem_2_sufficiency
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T01:58:48.587081+00:00
-- url     : https://prove2.me/submissions/db410349-bfbe-480c-b35f-66b6555fea6e

import Definitions.Def_ChoiceRM_MNL_Models

open ChoiceRM.MNL RevenueManagement
open scoped BigOperators

private lemma weight_nonneg {n : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (S : Finset (Fin n)) : 0 ≤ ∑ i ∈ S, w i :=
  Finset.sum_nonneg fun i _ => (hw i).le

private lemma probability_sum {n : ℕ} (w : Fin n → ℝ) (S : Finset (Fin n)) :
    purchaseProb (mnl w) S = (∑ i ∈ S, w i) / ((∑ i ∈ S, w i) + 1) := by
  simp only [purchaseProb, mnl]
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i hi => if_pos hi

private lemma probability_total {n : ℕ} (w : Fin n → ℝ) (S : Finset (Fin n)) :
    ∑ j, mnl w S j = (∑ i ∈ S, w i) / ((∑ i ∈ S, w i) + 1) := by
  simp only [mnl]
  simp [← Finset.sum_div]

private lemma complete_mem {n k : ℕ} {j : Fin n} : j ∈ complete n k ↔ j.val < k := by
  simp [complete]

private lemma complete_zero (n : ℕ) : complete n 0 = ∅ := by
  simp [complete]

private lemma complete_all (n : ℕ) : complete n n = Finset.univ := by
  ext j
  simp [complete, j.isLt]

private lemma complete_subset {n a b : ℕ} (hab : a ≤ b) : complete n a ⊆ complete n b := by
  intro j hj
  exact complete_mem.mpr (lt_of_lt_of_le (complete_mem.mp hj) hab)

private lemma ratio_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a / (a + 1) ≤ b / (b + 1) := by
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  nlinarith

private lemma ratio_strict {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    a / (a + 1) < b / (b + 1) := by
  apply (div_lt_div_iff₀ (by linarith) (by linarith)).mpr
  nlinarith

private lemma reciprocal_mixture (y₁ y₂ y₃ θ : ℝ)
    (h0 : 0 ≤ y₁) (h12 : y₁ ≤ y₂) (h23 : y₂ ≤ y₃)
    (h : θ * (y₁ / (y₁ + 1)) + (1 - θ) * (y₃ / (y₃ + 1)) = y₂ / (y₂ + 1)) :
    θ * (1 / (y₁ + 1)) + (1 - θ) * (1 / (y₃ + 1)) = 1 / (y₂ + 1) := by
  have hid (y : ℝ) (hy : 0 ≤ y) : 1 / (y + 1) = 1 - y / (y + 1) := by
    field_simp
    <;> linarith
  rw [hid y₁ h0, hid y₂ (by linarith), hid y₃ (by linarith)]
  nlinarith [h]

private lemma twoPoint_sum {n : ℕ} (k : ℕ) (hk : k < n) (θ : ℝ)
    (f : Fin (n + 1) → ℝ) :
    ∑ l, twoPoint k θ l * f l =
      θ * f ⟨k, by omega⟩ + (1 - θ) * f ⟨k + 1, by omega⟩ := by
  classical
  let k0 : Fin (n + 1) := ⟨k, by omega⟩
  let k1 : Fin (n + 1) := ⟨k + 1, by omega⟩
  have hne : k0 ≠ k1 := by intro h; have := congrArg Fin.val h; dsimp [k0, k1] at this; omega
  have he (l : Fin (n + 1)) : twoPoint k θ l * f l =
      (if l = k0 then θ * f k0 else 0) +
      (if l = k1 then (1 - θ) * f k1 else 0) := by
    by_cases h0 : l = k0
    · subst l
      simp [twoPoint, k0, hne]
    · by_cases h1 : l = k1
      · subst l
        simp [twoPoint, k1, h0, show k + 1 ≠ k by omega]
      · have hv0 : l.val ≠ k := fun h => h0 (Fin.ext h)
        have hv1 : l.val ≠ k + 1 := fun h => h1 (Fin.ext h)
        simp [twoPoint, hv0, hv1, h0, h1]
  simp_rw [he, Finset.sum_add_distrib]
  simp [k0, k1]

private lemma mix_twoPoint {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ)
    (k : ℕ) (hk : k < n) (θ : ℝ) (j : Fin n) :
    mixProb P (twoPoint k θ) j =
      θ * P (complete n k) j + (1 - θ) * P (complete n (k + 1)) j := by
  exact twoPoint_sum k hk θ (fun l => P (complete n l.val) j)

private lemma probability_nonneg {n : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (S : Finset (Fin n)) (j : Fin n) : 0 ≤ mnl w S j := by
  unfold mnl
  split_ifs
  · exact div_nonneg (hw j).le (by linarith [weight_nonneg w hw S])
  · rfl

private lemma probability_partial_total {n : ℕ} (w : Fin n → ℝ)
    (A B : Finset (Fin n)) (hAB : A ⊆ B) :
    ∑ j ∈ B, mnl w A j = (∑ i ∈ A, w i) / ((∑ i ∈ A, w i) + 1) := by
  rw [← probability_sum]
  unfold purchaseProb
  symm
  apply Finset.sum_subset hAB
  intro j hj hjA
  simp [mnl, hjA]



private def zeroExtend {n : ℕ} (f : Fin n → ℝ) (i : ℕ) : ℝ :=
  if hi : i < n then f ⟨i, hi⟩ else 0

private lemma prefix_range {n : ℕ} (f : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∑ i ∈ Finset.range k, zeroExtend f i = ∑ j ∈ complete n k, f j := by
  classical
  apply Finset.sum_bij (fun i hi => (⟨i, lt_of_lt_of_le (Finset.mem_range.mp hi) hk⟩ : Fin n))
  · intro i hi
    exact complete_mem.mpr (Finset.mem_range.mp hi)
  · intro i hi j hj h
    exact congrArg Fin.val h
  · intro j hj
    refine ⟨j.val, Finset.mem_range.mpr (complete_mem.mp hj), ?_⟩
    rfl
  · intro i hi
    simp [zeroExtend, lt_of_lt_of_le (Finset.mem_range.mp hi) hk]

private lemma majorized_dot {n : ℕ} (x a b : Fin n → ℝ) (hx : Antitone x)
    (hp : ∀ k, k < n → ∑ j ∈ complete n k, a j ≤ ∑ j ∈ complete n k, b j)
    (ht : ∑ j, b j = ∑ j, a j) :
    ∑ j, x j * a j ≤ ∑ j, x j * b j := by
  let d : Fin n → ℝ := fun j => b j - a j
  have htot : ∑ i ∈ Finset.range n, zeroExtend d i = 0 := by
    rw [prefix_range d n le_rfl, complete_all]
    simp [d, Finset.sum_sub_distrib, ht]
  have hpref (k : ℕ) (hk : k < n) :
      0 ≤ ∑ i ∈ Finset.range k, zeroExtend d i := by
    rw [prefix_range d k hk.le]
    simpa [d, Finset.sum_sub_distrib] using sub_nonneg.mpr (hp k hk)
  have hs : (∑ i ∈ Finset.range (n - 1),
      (zeroExtend x (i + 1) - zeroExtend x i) *
        (∑ j ∈ Finset.range (i + 1), zeroExtend d j)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    have hi0 : i < n := by have := Finset.mem_range.mp hi; omega
    have hi1 : i + 1 < n := by have := Finset.mem_range.mp hi; omega
    apply mul_nonpos_of_nonpos_of_nonneg
    · simp only [zeroExtend, dif_pos hi0, dif_pos hi1]
      exact sub_nonpos.mpr (hx (show (⟨i, hi0⟩ : Fin n) ≤ ⟨i + 1, hi1⟩ by change i ≤ i + 1; omega))
    · exact hpref (i + 1) hi1
  have hab := Finset.sum_range_by_parts (zeroExtend x) (zeroExtend d) n
  simp only [smul_eq_mul, htot, mul_zero, zero_sub] at hab
  have hpositive : 0 ≤ ∑ i ∈ Finset.range n, zeroExtend x i * zeroExtend d i := by
    rw [hab]
    linarith
  have hsame : (∑ i ∈ Finset.range n, zeroExtend x i * zeroExtend d i) =
      ∑ j, x j * d j := by
    calc
      _ = ∑ i ∈ Finset.range n, zeroExtend (fun j => x j * d j) i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [zeroExtend, Finset.mem_range.mp hi]
      _ = _ := by rw [prefix_range _ n le_rfl, complete_all]
  rw [hsame] at hpositive
  simpa [d, mul_sub, Finset.sum_sub_distrib] using hpositive

private lemma fareValue_total {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ)
    (hsupp : SupportedOn P) (x : Fin n → ℝ) (S : Finset (Fin n)) :
    fareValue P x S = ∑ j, x j * P S j := by
  apply Finset.sum_subset (Finset.subset_univ S)
  intro j _ hj
  rw [hsupp S j hj, mul_zero]



open RevenueManagement

/-- Theorem 2 (⇐), p. 19: if (i) the purchase probability `Q` is increasing and (ii) for every
incomplete set `T` some convex combination `P̄(α)` of the complete sets majorizes
`(P_1(T), …, P_n(T))`, then the choice model has the nested-by-fare-order property. -/
theorem solution {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ)
    (hP : IsChoiceModel P) (hsupp : SupportedOn P)
    (hi : ∀ S T : Finset (Fin n), S ⊆ T → purchaseProb P S ≤ purchaseProb P T)
    (hii : ∀ T : Finset (Fin n), ¬ IsComplete T →
      ∃ α : Fin (n + 1) → ℝ, (∀ k, 0 ≤ α k) ∧ ∑ k, α k = 1 ∧
        (∀ i, i < n → ∑ j ∈ complete n i, P T j ≤ ∑ j ∈ complete n i, mixProb P α j) ∧
        ∑ j, mixProb P α j = ∑ j, P T j) :
    HasFareOrderNesting P := by
  classical
  refine ⟨hi, ?_⟩
  intro x hx
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (n + 1)))
    (fun k => fareValue P x (complete n k.val)) Finset.univ_nonempty
  refine ⟨k.val, by omega, ?_⟩
  intro S
  by_cases hS : IsComplete S
  · obtain ⟨l, hl, rfl⟩ := hS
    exact hk ⟨l, by omega⟩ (Finset.mem_univ _)
  · obtain ⟨α, hα, hαsum, hp, ht⟩ := hii S hS
    calc
      fareValue P x S = ∑ j, x j * P S j := fareValue_total P hsupp x S
      _ ≤ ∑ j, x j * mixProb P α j := majorized_dot x _ _ hx hp ht
      _ = ∑ l, α l * fareValue P x (complete n l.val) := by
        simp only [mixProb, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro l _
        rw [fareValue_total P hsupp x, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ ∑ l, α l * fareValue P x (complete n k.val) := by
        exact Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left
          (hk l (Finset.mem_univ _)) (hα l)
      _ = fareValue P x (complete n k.val) := by rw [← Finset.sum_mul, hαsum, one_mul]


