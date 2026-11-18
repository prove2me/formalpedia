-- Prove2me | solution 1 for ConsumerUtilityApprox.UnitDemand.eq_5_11
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T18:07:58.522013+00:00
-- url     : https://prove2.me/submissions/69ae956f-f3ce-4cfe-80ee-9ce3c01e2e30

import Mathlib
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Mechanisms


open scoped BigOperators

namespace Utility7.FairProof

noncomputable def weight {α : Type*} [DecidableEq α] (q : α → ℝ)
    (s A : Finset α) : ℝ := ∏ k ∈ s, if k ∈ A then q k else 1 - q k

variable {α : Type*} [DecidableEq α] (q : α → ℝ)

lemma weight_insert_absent {s A : Finset α} {k : α} (hk : k ∉ s)
    (hA : A ⊆ s) : weight q (insert k s) A = (1 - q k) * weight q s A := by
  have hkA : k ∉ A := fun h => hk (hA h)
  simp [weight, Finset.prod_insert, hk, hkA]

lemma weight_insert_present {s A : Finset α} {k : α} (hk : k ∉ s)
    (hA : A ⊆ s) : weight q (insert k s) (insert k A) = q k * weight q s A := by
  rw [weight, Finset.prod_insert hk]
  simp only [Finset.mem_insert_self, if_true]
  congr 1
  apply Finset.prod_congr rfl
  intro x hx
  have hxk : x ≠ k := fun h => hk (h ▸ hx)
  simp [hxk]

lemma sum_weight (s : Finset α) : ∑ A ∈ s.powerset, weight q s A = 1 := by
  induction s using Finset.induction_on with
  | empty => simp [weight]
  | @insert k s hk ih =>
    rw [Finset.sum_powerset_insert hk]
    calc
      _ = ∑ A ∈ s.powerset, ((1 - q k) * weight q s A + q k * weight q s A) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro A hA
        rw [weight_insert_absent q hk (Finset.mem_powerset.mp hA),
          weight_insert_present q hk (Finset.mem_powerset.mp hA)]
      _ = ∑ A ∈ s.powerset, weight q s A := by congr 1; funext A; ring
      _ = 1 := ih

/-- Insertion of a single independent Bernoulli request. -/
lemma coordinate_balance (s : Finset α) (k : α) (hk : k ∈ s) :
    (∑ A ∈ s.powerset, weight q s A *
      (if k ∈ A then q k / (A.card : ℝ) else q k / ((A.card : ℝ) + 1))) =
    ∑ A ∈ s.powerset, weight q s A * (if k ∈ A then 1 / (A.card : ℝ) else 0) := by
  let t := s.erase k
  have hkt : k ∉ t := Finset.notMem_erase _ _
  have hs : s = insert k t := (Finset.insert_erase hk).symm
  rw [hs, Finset.sum_powerset_insert hkt, Finset.sum_powerset_insert hkt]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A hA
  have hAt : A ⊆ t := Finset.mem_powerset.mp hA
  have hkA : k ∉ A := fun h => hkt (hAt h)
  rw [weight_insert_absent q hkt hAt, weight_insert_present q hkt hAt]
  simp only [hkA, if_false, Finset.mem_insert_self, if_true,
    Finset.card_insert_of_notMem hkA, Nat.cast_add, Nat.cast_one, mul_zero, add_zero]
  ring

lemma numerator_eq_sum (s A : Finset α) (hA : A ⊆ s) :
    (∑ k ∈ A, q k) / (A.card : ℝ) +
      (∑ k ∈ s \ A, q k) / ((A.card : ℝ) + 1) =
    ∑ k ∈ s, if k ∈ A then q k / (A.card : ℝ) else q k / ((A.card : ℝ) + 1) := by
  rw [Finset.sum_ite]
  have hfilter : s.filter (fun k => k ∈ A) = A := by
    ext k
    simp only [Finset.mem_filter, and_iff_right_iff_imp]
    exact fun h => hA h
  have hfilter' : s.filter (fun k => k ∉ A) = s \ A := by ext k; simp
  rw [hfilter, hfilter', Finset.sum_div, Finset.sum_div]

lemma sum_reciprocal (s A : Finset α) (hA : A ⊆ s) :
    (∑ k ∈ s, if k ∈ A then 1 / (A.card : ℝ) else 0) =
      if A = ∅ then 0 else 1 := by
  rw [Finset.sum_ite]
  have hfilter : s.filter (fun k => k ∈ A) = A := by
    ext k
    simp only [Finset.mem_filter, and_iff_right_iff_imp]
    exact fun h => hA h
  rw [hfilter]
  by_cases he : A = ∅
  · simp [he]
  · have hc : (A.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr he))
    simp [he, hc]

lemma sum_numerator (s : Finset α) :
    (∑ A ∈ s.powerset, weight q s A *
      ((∑ k ∈ A, q k) / (A.card : ℝ) +
        (∑ k ∈ s \ A, q k) / ((A.card : ℝ) + 1))) =
      1 - weight q s ∅ := by
  calc
    _ = ∑ A ∈ s.powerset, weight q s A *
        ∑ k ∈ s, if k ∈ A then q k / (A.card : ℝ) else q k / ((A.card : ℝ) + 1) := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [numerator_eq_sum q s A (Finset.mem_powerset.mp hA)]
    _ = ∑ k ∈ s, ∑ A ∈ s.powerset, weight q s A *
        (if k ∈ A then q k / (A.card : ℝ) else q k / ((A.card : ℝ) + 1)) := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ k ∈ s, ∑ A ∈ s.powerset, weight q s A *
        (if k ∈ A then 1 / (A.card : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact coordinate_balance q s k hk
    _ = ∑ A ∈ s.powerset, weight q s A *
        (if A = ∅ then 0 else 1) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A hA
      rw [← Finset.mul_sum, sum_reciprocal s A (Finset.mem_powerset.mp hA)]
    _ = (∑ A ∈ s.powerset, weight q s A) - weight q s ∅ := by
      have he : ∅ ∈ s.powerset := by simp
      simp only [mul_ite, mul_zero, mul_one]
      have hh : (∑ A ∈ s.powerset, if A = ∅ then 0 else weight q s A) =
          ∑ A ∈ s.powerset.erase ∅, weight q s A := by
        rw [← Finset.sum_erase_add _ _ he]
        simp only [ite_true, add_zero]
        apply Finset.sum_congr rfl
        intro A hA
        simp [Finset.ne_of_mem_erase hA]
      rw [hh]
      have hh' := Finset.sum_erase_add s.powerset (weight q s) he
      linarith
    _ = 1 - weight q s ∅ := by rw [sum_weight]

end Utility7.FairProof


open scoped BigOperators

namespace Utility7.FairProof

lemma product_failure_le_exp {α : Type*} [DecidableEq α] (s : Finset α) (q : α → ℝ)
    (hq : ∀ k ∈ s, 0 ≤ q k ∧ q k ≤ 1) :
    (∏ k ∈ s, (1 - q k)) ≤ Real.exp (-(∑ k ∈ s, q k)) := by
  calc
    _ ≤ ∏ k ∈ s, Real.exp (-q k) := by
      apply Finset.prod_le_prod
      · intro k hk
        linarith [(hq k hk).2]
      · intro k hk
        have h := Real.add_one_le_exp (-q k)
        linarith
    _ = Real.exp (-(∑ k ∈ s, q k)) := by
      rw [← Real.exp_sum]
      congr 1
      simp

lemma exponential_chord {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp (-s) ≤ 1 - (1 - Real.exp (-1)) * s := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-1 : ℝ))
    (show 0 ≤ 1 - s by linarith) hs (show 1 - s + s = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_neg, mul_one, Real.exp_zero] at h
  nlinarith

lemma selection_lower_bound {α : Type*} [DecidableEq α] (s : Finset α) (q : α → ℝ)
    (hq : ∀ k ∈ s, 0 ≤ q k ∧ q k ≤ 1)
    (hs : ∑ k ∈ s, q k ≤ 1) (hpos : 0 < ∑ k ∈ s, q k) :
    1 - Real.exp (-1) ≤ (1 - ∏ k ∈ s, (1 - q k)) / ∑ k ∈ s, q k := by
  apply (le_div_iff₀ hpos).mpr
  have hprod := product_failure_le_exp s q hq
  have hchord := exponential_chord (le_of_lt hpos) hs
  linarith

end Utility7.FairProof


open scoped BigOperators
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.FairProof

lemma scaled_fair {n m : ℕ} (Q : Fin n → Fin m → ℝ) (j : Fin m) (i : Fin n)
    (hS : ∑ k, Q k j ≠ 0) (A : Finset (Fin n)) (hA : A ⊆ Finset.univ.erase i) :
    (∑ k, Q k j) * fairSelProb Q j (insert i A) i =
      ((∑ k ∈ A, Q k j) / (A.card : ℝ) +
        (∑ k ∈ (Finset.univ.erase i) \ A, Q k j) / ((A.card : ℝ) + 1)) +
      if A = ∅ then Q i j else 0 := by
  have hiA : i ∉ A := fun hi => Finset.notMem_erase i Finset.univ (hA hi)
  by_cases he : A = ∅
  · subst A
    simp only [fairSelProb, Finset.insert_empty, Finset.mem_singleton, not_true_eq_false,
      if_false, Finset.card_singleton, if_true, mul_one, Finset.sum_empty, Finset.card_empty,
      Nat.cast_zero, zero_div, Finset.sdiff_empty, zero_add, div_one]
    exact (Finset.sum_erase_add Finset.univ (fun k => Q k j) (Finset.mem_univ i)).symm
  · have hcard : (insert i A).card ≠ 1 := by
      rw [Finset.card_insert_of_notMem hiA]
      have hnon := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
      omega
    have herase : (insert i A).erase i = A := Finset.erase_insert hiA
    have hcard' : A.card + 1 ≠ 1 := by
      simpa only [Finset.card_insert_of_notMem hiA] using hcard
    have hdiff : Finset.univ \ insert i A = (Finset.univ.erase i) \ A := by
      ext k
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_erase]
      tauto
    simp only [fairSelProb, Finset.mem_insert_self, not_true_eq_false, if_false, hcard,
      hS, herase, hdiff, Finset.card_insert_of_notMem hiA, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_right, he, add_zero, hcard']
    rw [← mul_assoc, mul_one_div_cancel hS, one_mul]

lemma fair_expectation_nonzero {n m : ℕ} (Q : Fin n → Fin m → ℝ) (j : Fin m)
    (i : Fin n) (hS : ∑ k, Q k j ≠ 0) :
    (∑ A ∈ (Finset.univ.erase i).powerset,
        weight (fun k => Q k j) (Finset.univ.erase i) A * fairSelProb Q j (insert i A) i) =
      selectionConst Q j := by
  let s : Finset (Fin n) := Finset.univ.erase i
  let q : Fin n → ℝ := fun k => Q k j
  have hnum := sum_numerator q s
  have hscaled : (∑ k, Q k j) *
      (∑ A ∈ s.powerset, weight q s A * fairSelProb Q j (insert i A) i) =
        (1 - weight q s ∅) + weight q s ∅ * Q i j := by
    calc
      _ = ∑ A ∈ s.powerset, weight q s A *
          ((∑ k, Q k j) * fairSelProb Q j (insert i A) i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro A hA
        ring
      _ = ∑ A ∈ s.powerset, weight q s A *
          (((∑ k ∈ A, q k) / (A.card : ℝ) +
            (∑ k ∈ s \ A, q k) / ((A.card : ℝ) + 1)) +
          if A = ∅ then Q i j else 0) := by
        apply Finset.sum_congr rfl
        intro A hA
        rw [scaled_fair Q j i hS A (Finset.mem_powerset.mp hA)]
      _ = _ := by
        simp_rw [mul_add] at hnum ⊢
        rw [Finset.sum_add_distrib, hnum]
        simp
  have hprod : (∏ k, (1 - Q k j)) = (1 - Q i j) * weight q s ∅ := by
    rw [← Finset.mul_prod_erase Finset.univ (fun k => 1 - Q k j) (Finset.mem_univ i)]
    rfl
  unfold selectionConst
  rw [if_neg hS]
  apply (eq_div_iff hS).mpr
  change (∑ A ∈ s.powerset, weight q s A * fairSelProb Q j (insert i A) i) *
      (∑ k, Q k j) = _
  rw [mul_comm, hscaled, hprod]
  ring

lemma fair_expectation_zero {n m : ℕ} (Q : Fin n → Fin m → ℝ) (j : Fin m)
    (i : Fin n) (hQ : ∀ k, 0 ≤ Q k j) (hS : ∑ k, Q k j = 0) :
    (∑ A ∈ (Finset.univ.erase i).powerset,
        weight (fun k => Q k j) (Finset.univ.erase i) A * fairSelProb Q j (insert i A) i) =
      selectionConst Q j := by
  have hz : ∀ k, Q k j = 0 := by
    intro k
    have h := Finset.single_le_sum (fun k _ => hQ k) (Finset.mem_univ k)
    rw [hS] at h
    exact le_antisymm h (hQ k)
  rw [selectionConst, if_pos hS]
  trans weight (fun k => Q k j) (Finset.univ.erase i) ∅ * fairSelProb Q j (insert i ∅) i
  · apply Finset.sum_eq_single ∅
    · intro A hA hne
      have hnon : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
      obtain ⟨k, hk⟩ := hnon
      have hks := (Finset.mem_powerset.mp hA) hk
      have hw : weight (fun k => Q k j) (Finset.univ.erase i) A = 0 := by
        apply Finset.prod_eq_zero hks
        simp [hk, hz k]
      simp [hw]
    · simp
  · simp [weight, fairSelProb, hz]

theorem eq_5_11 {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (Q : Fin n → Fin m → ℝ)
    (hQ : ∀ k j, 0 ≤ Q k j ∧ Q k j ≤ 1) (hfeas : ∀ j, ∑ k, Q k j ≤ 1)
    (j : Fin m) (i : Fin n) :
    (∑ A ∈ (Finset.univ.erase i).powerset,
        (∏ k ∈ Finset.univ.erase i, if k ∈ A then Q k j else 1 - Q k j) *
          fairSelProb Q j (insert i A) i) = selectionConst Q j ∧
      1 - Real.exp (-1) ≤ selectionConst Q j := by
  constructor
  · by_cases hS : ∑ k, Q k j = 0
    · exact fair_expectation_zero Q j i (fun k => (hQ k j).1) hS
    · exact fair_expectation_nonzero Q j i hS
  · unfold selectionConst
    split_ifs with hS
    · linarith [Real.exp_pos (-1)]
    · have hnonneg : 0 ≤ ∑ k, Q k j := Finset.sum_nonneg (fun k _ => (hQ k j).1)
      exact selection_lower_bound Finset.univ (fun k => Q k j) (fun k _ => hQ k j)
        (hfeas j) (lt_of_le_of_ne hnonneg (Ne.symm hS))

end Utility7.FairProof

open ConsumerUtilityApprox.UnitDemand
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem solution {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (Q : Fin n → Fin m → ℝ)
    (hQ : ∀ k j, 0 ≤ Q k j ∧ Q k j ≤ 1) (hfeas : ∀ j, ∑ k, Q k j ≤ 1)
    (j : Fin m) (i : Fin n) :
    (∑ A ∈ (Finset.univ.erase i).powerset,
        (∏ k ∈ Finset.univ.erase i, if k ∈ A then Q k j else 1 - Q k j) *
          fairSelProb Q j (insert i A) i) = selectionConst Q j ∧
      1 - Real.exp (-1) ≤ selectionConst Q j  := Utility7.FairProof.eq_5_11 hn hm Q hQ hfeas j i
