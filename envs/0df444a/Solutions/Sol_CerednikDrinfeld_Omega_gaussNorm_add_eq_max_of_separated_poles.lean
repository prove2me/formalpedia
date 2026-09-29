-- Prove2me | solution 1 for CerednikDrinfeld.Omega.gaussNorm_add_eq_max_of_separated_poles
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/64230986-645b-5af6-885c-dcf1fbaa75ae

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_gaussNorm_add_eq_max_of_separated_poles

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial

namespace IdOrth

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

def gauss (P : K[X]) : Γ₀ := P.support.sup fun i => Valued.v (P.coeff i)

theorem v_coeff_le_gauss (P : K[X]) (i : ℕ) : v (P.coeff i) ≤ gauss P := by
  by_cases h : i ∈ P.support
  · exact Finset.le_sup (f := fun i => v (P.coeff i)) h
  · rw [Polynomial.notMem_support_iff.1 h, map_zero]; exact zero_le'

theorem gauss_le {P : K[X]} {γ : Γ₀} (h : ∀ i, v (P.coeff i) ≤ γ) : gauss P ≤ γ :=
  Finset.sup_le fun i _ => h i

theorem gauss_zero : gauss (0 : K[X]) = 0 := by simp [gauss, bot_eq_zero]

theorem exists_eq_gauss {P : K[X]} (hP : P ≠ 0) : ∃ i ∈ P.support, v (P.coeff i) = gauss P := by
  obtain ⟨i, hi, h⟩ := Finset.exists_mem_eq_sup P.support (Polynomial.support_nonempty.2 hP)
    (fun i => v (P.coeff i))
  exact ⟨i, hi, h.symm⟩

theorem gauss_pos {P : K[X]} (hP : P ≠ 0) : 0 < gauss P := by
  obtain ⟨i, hi, h⟩ := exists_eq_gauss hP
  rw [← h, Valuation.pos_iff]
  exact Polynomial.mem_support_iff.1 hi

theorem gauss_ne_zero {P : K[X]} (hP : P ≠ 0) : gauss P ≠ 0 := (gauss_pos hP).ne'

theorem gauss_lt {P : K[X]} {γ : Γ₀} (hγ : γ ≠ 0) (h : ∀ i, v (P.coeff i) < γ) : gauss P < γ := by
  by_cases hP : P = 0
  · rw [hP, gauss_zero]; exact zero_lt_iff.2 hγ
  · obtain ⟨i, -, hi⟩ := exists_eq_gauss hP
    rw [← hi]; exact h i

theorem gauss_C_mul (a : K) (P : K[X]) : gauss (C a * P) = v a * gauss P := by
  apply le_antisymm
  · exact gauss_le fun i => by rw [coeff_C_mul, map_mul]; exact mul_le_mul' le_rfl (v_coeff_le_gauss P i)
  · by_cases ha : a = 0
    · rw [ha, map_zero, zero_mul]; exact zero_le'
    by_cases hP : P = 0
    · rw [hP, gauss_zero, mul_zero]; exact zero_le'
    obtain ⟨i, -, hi⟩ := exists_eq_gauss hP
    calc v a * gauss P = v ((C a * P).coeff i) := by rw [coeff_C_mul, map_mul, hi]
      _ ≤ gauss (C a * P) := v_coeff_le_gauss _ _

theorem gauss_C (a : K) : gauss (C a : K[X]) = v a := by
  apply le_antisymm
  · exact gauss_le fun i => by
      rw [coeff_C]; split_ifs
      · exact le_rfl
      · rw [map_zero]; exact zero_le'
  · simpa using v_coeff_le_gauss (C a) 0

theorem gauss_one : gauss (1 : K[X]) = 1 := by rw [← C_1, gauss_C, map_one]

theorem gauss_add_le (P Q : K[X]) : gauss (P + Q) ≤ max (gauss P) (gauss Q) :=
  gauss_le fun i => by
    rw [coeff_add]
    exact (Valuation.map_add _ _ _).trans (max_le_max (v_coeff_le_gauss P i) (v_coeff_le_gauss Q i))

theorem gauss_neg (P : K[X]) : gauss (-P) = gauss P := by
  simp only [gauss, support_neg, coeff_neg, Valuation.map_neg]

theorem gauss_sub_le (P Q : K[X]) : gauss (P - Q) ≤ max (gauss P) (gauss Q) := by
  rw [sub_eq_add_neg, ← gauss_neg Q]; exact gauss_add_le P (-Q)

theorem gauss_add_eq_of_lt {P Q : K[X]} (h : gauss Q < gauss P) : gauss (P + Q) = gauss P := by
  apply le_antisymm ((gauss_add_le P Q).trans (max_le le_rfl h.le))
  have hP : P ≠ 0 := by rintro rfl; rw [gauss_zero] at h; exact not_lt_of_ge zero_le' h
  obtain ⟨i, -, hi⟩ := exists_eq_gauss hP
  have hlt : v (Q.coeff i) < v (P.coeff i) := (v_coeff_le_gauss Q i).trans_lt (hi ▸ h)
  calc gauss P = v ((P + Q).coeff i) := by rw [coeff_add, Valuation.map_add_eq_of_lt_left _ hlt, hi]
    _ ≤ gauss (P + Q) := v_coeff_le_gauss _ _

theorem v_eval_le_gauss (P : K[X]) {y : K} (hy : v y ≤ 1) : v (P.eval y) ≤ gauss P := by
  rw [eval_eq_sum_range]
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [map_mul, map_pow]
  exact (mul_le_mul' le_rfl (pow_le_one₀ zero_le' hy)).trans (by rw [mul_one]; exact v_coeff_le_gauss P i)

theorem gauss_mul_X_sub_C (P : K[X]) (α : K) : gauss (P * (X - C α)) = gauss P * max 1 (v α) := by
  by_cases hP : P = 0
  · rw [hP, zero_mul, gauss_zero, zero_mul]

  have hc0 : (P * (X - C α)).coeff 0 = -(P.coeff 0 * α) := by
    rw [mul_sub, coeff_sub, coeff_mul_X_zero, coeff_mul_C, zero_sub]
  have hcs : ∀ a : ℕ, (P * (X - C α)).coeff (a + 1) = P.coeff a - P.coeff (a + 1) * α := fun a =>
    coeff_mul_X_sub_C
  apply le_antisymm
  · refine gauss_le fun i => ?_
    rcases i with _ | a
    · rw [hc0, Valuation.map_neg, map_mul]
      exact mul_le_mul' (v_coeff_le_gauss P 0) (le_max_right _ _)
    · rw [hcs]
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
      · calc v (P.coeff a) = v (P.coeff a) * 1 := (mul_one _).symm
          _ ≤ gauss P * max 1 (v α) := mul_le_mul' (v_coeff_le_gauss P a) (le_max_left _ _)
      · rw [map_mul]; exact mul_le_mul' (v_coeff_le_gauss P _) (le_max_right _ _)
  ·
    classical
    let I : Finset ℕ := P.support.filter fun i => v (P.coeff i) = gauss P
    have hI : I.Nonempty := by
      obtain ⟨i, hi, h⟩ := exists_eq_gauss hP
      exact ⟨i, Finset.mem_filter.2 ⟨hi, h⟩⟩
    have hIspec : ∀ i ∈ I, v (P.coeff i) = gauss P := fun i hi => (Finset.mem_filter.1 hi).2
    have hlt_of_notMem : ∀ i, i ∉ I → v (P.coeff i) < gauss P := fun i hi => by
      refine lt_of_le_of_ne (v_coeff_le_gauss P i) fun h => hi ?_
      refine Finset.mem_filter.2 ⟨Polynomial.mem_support_iff.2 fun h0 => ?_, h⟩
      rw [h0, map_zero] at h; exact gauss_ne_zero hP h.symm
    rcases le_or_gt (v α) 1 with hα | hα
    ·
      rw [max_eq_left hα, mul_one]
      set j := I.max' hI with hj
      have hjI : j ∈ I := Finset.max'_mem I hI
      have hj1 : v (P.coeff (j + 1)) < gauss P := hlt_of_notMem _ fun h =>
        absurd (Finset.le_max' I _ h) (by rw [← hj]; omega)
      have hlt : v (P.coeff (j + 1) * α) < v (P.coeff j) := by
        rw [map_mul, hIspec j hjI]
        exact lt_of_le_of_lt (mul_le_mul' le_rfl hα) (by rw [mul_one]; exact hj1)
      calc gauss P = v ((P * (X - C α)).coeff (j + 1)) := by
            rw [hcs, Valuation.map_sub_eq_of_lt_left _ hlt, hIspec j hjI]
        _ ≤ gauss (P * (X - C α)) := v_coeff_le_gauss _ _
    ·
      rw [max_eq_right hα.le]
      have key : ∀ j, j = I.min' hI → v ((P * (X - C α)).coeff j) = gauss P * v α := by
        intro j hj
        have hjI : j ∈ I := hj ▸ Finset.min'_mem I hI
        rcases j with _ | a
        · rw [hc0, Valuation.map_neg, map_mul, hIspec _ hjI]
        · have ha : v (P.coeff a) < gauss P := hlt_of_notMem _ fun h =>
            absurd (Finset.min'_le I _ h) (by rw [← hj]; omega)
          have hlt : v (P.coeff a) < v (P.coeff (a + 1) * α) := by
            rw [map_mul, hIspec _ hjI]
            exact lt_of_lt_of_le ha (le_of_lt (lt_of_le_of_lt (mul_one _).symm.le
              (mul_lt_mul_of_pos_left hα (gauss_pos hP))))
          rw [hcs, Valuation.map_sub_eq_of_lt_right _ hlt, map_mul, hIspec _ hjI]
      calc gauss P * v α = v ((P * (X - C α)).coeff (I.min' hI)) := (key _ rfl).symm
        _ ≤ gauss (P * (X - C α)) := v_coeff_le_gauss _ _

theorem gauss_mul_prod_X_sub_C (P : K[X]) (s : Multiset K) :
    gauss (P * (s.map fun α => X - C α).prod) = gauss P * (s.map fun α => max 1 (v α)).prod := by
  induction s using Multiset.induction_on generalizing P with
  | empty => simp
  | cons α s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ← mul_assoc, ih, gauss_mul_X_sub_C, Multiset.map_cons,
      Multiset.prod_cons, mul_assoc]

section AlgClosed

variable [IsAlgClosed K]

theorem eq_C_mul_prod (P : K[X]) : P = C P.leadingCoeff * (P.roots.map fun α => X - C α).prod :=
  (C_leadingCoeff_mul_prod_multiset_X_sub_C
    ((splits_iff_card_roots.1 (IsAlgClosed.splits P)).symm ▸ rfl)).symm

theorem gauss_eq_prod_roots (P : K[X]) :
    gauss P = v P.leadingCoeff * (P.roots.map fun α => max 1 (v α)).prod := by
  conv_lhs => rw [eq_C_mul_prod P]
  rw [gauss_mul_prod_X_sub_C, gauss_C]

theorem gauss_mul (P Q : K[X]) : gauss (P * Q) = gauss P * gauss Q := by
  by_cases hP : P = 0
  · rw [hP, zero_mul, gauss_zero, zero_mul]
  by_cases hQ : Q = 0
  · rw [hQ, mul_zero, gauss_zero, mul_zero]
  rw [gauss_eq_prod_roots, gauss_eq_prod_roots P, gauss_eq_prod_roots Q, leadingCoeff_mul, map_mul,
    roots_mul (mul_ne_zero hP hQ), Multiset.map_add, Multiset.prod_add]
  exact mul_mul_mul_comm _ _ _ _

theorem v_eval_eq_gauss (P : K[X]) {y : K} (hy : v y ≤ 1)
    (hgen : ∀ α ∈ P.roots, v α ≤ 1 → 1 ≤ v (y - α)) : v (P.eval y) = gauss P := by
  conv_lhs => rw [eq_C_mul_prod P]
  rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, map_mul, map_multiset_prod, Multiset.map_map,
    gauss_eq_prod_roots]
  congr 1
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun α hα => ?_)
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
  rcases le_or_gt (v α) 1 with h | h
  · rw [max_eq_left h]
    exact le_antisymm ((Valuation.map_sub _ _ _).trans (max_le hy h)) (hgen α hα h)
  · rw [max_eq_right h.le]
    exact Valuation.map_sub_eq_of_lt_right _ (hy.trans_lt h)

theorem gauss_eq_coeff_zero_of_roots (Q : K[X]) (h : ∀ α ∈ Q.roots, 1 ≤ v α) : gauss Q = v (Q.coeff 0) := by
  rw [(IsAlgClosed.splits Q).coeff_zero_eq_leadingCoeff_mul_prod_roots, map_mul, map_mul, map_pow,
    Valuation.map_neg, map_one, one_pow, one_mul, gauss_eq_prod_roots, map_multiset_prod]
  congr 1
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun α hα => max_eq_right (h α hα))

end AlgClosed

end IdOrth

namespace IdOrth

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

theorem prod_X_sub_C_coeff_of_lt_one (s : Multiset K) (hs : ∀ α ∈ s, v α < 1) :
    (∀ i, v (((s.map fun α => X - C α).prod).coeff i) ≤ 1) ∧
      ∀ i < Multiset.card s, v (((s.map fun α => X - C α).prod).coeff i) < 1 := by
  induction s using Multiset.induction_on with
  | empty =>
    refine ⟨fun i => ?_, fun i hi => absurd hi (by simp)⟩
    simp only [Multiset.map_zero, Multiset.prod_zero, coeff_one]
    split_ifs
    · rw [map_one]
    · rw [map_zero]; exact zero_le'
  | cons α s ih =>
    have hα : v α < 1 := hs α (Multiset.mem_cons_self _ _)
    obtain ⟨ih1, ih2⟩ := ih fun β hβ => hs β (Multiset.mem_cons_of_mem hβ)
    set M := (s.map fun α => X - C α).prod with hM
    have hprod : ((α ::ₘ s).map fun α => X - C α).prod = M * (X - C α) := by
      rw [Multiset.map_cons, Multiset.prod_cons, mul_comm]
    have hc0 : (M * (X - C α)).coeff 0 = -(M.coeff 0 * α) := by
      rw [mul_sub, coeff_sub, coeff_mul_X_zero, coeff_mul_C, zero_sub]
    have hcs : ∀ a : ℕ, (M * (X - C α)).coeff (a + 1) = M.coeff a - M.coeff (a + 1) * α := fun a =>
      coeff_mul_X_sub_C
    have hbound : ∀ a, v (M.coeff a * α) < 1 := fun a => by
      rw [map_mul]
      exact (mul_le_mul' (ih1 a) le_rfl).trans_lt (by rwa [one_mul])
    rw [hprod, Multiset.card_cons]
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · rcases i with _ | a
      · rw [hc0, Valuation.map_neg]; exact (hbound 0).le
      · rw [hcs]; exact (Valuation.map_sub _ _ _).trans (max_le (ih1 a) (hbound _).le)
    · rcases i with _ | a
      · rw [hc0, Valuation.map_neg]; exact hbound 0
      · rw [hcs]
        exact (Valuation.map_sub _ _ _).trans_lt (max_lt (ih2 a (by omega)) (hbound _))

theorem prod_X_sub_C_coeff_of_le_one (s : Multiset K) (hs : ∀ α ∈ s, v α ≤ 1) :
    ∀ i, v (((s.map fun α => X - C α).prod).coeff i) ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty =>
    intro i
    simp only [Multiset.map_zero, Multiset.prod_zero, coeff_one]
    split_ifs
    · rw [map_one]
    · rw [map_zero]; exact zero_le'
  | cons α s ih =>
    have hα : v α ≤ 1 := hs α (Multiset.mem_cons_self _ _)
    have ih1 := ih fun β hβ => hs β (Multiset.mem_cons_of_mem hβ)
    set M := (s.map fun α => X - C α).prod with hM
    have hprod : ((α ::ₘ s).map fun α => X - C α).prod = M * (X - C α) := by
      rw [Multiset.map_cons, Multiset.prod_cons, mul_comm]
    have hc0 : (M * (X - C α)).coeff 0 = -(M.coeff 0 * α) := by
      rw [mul_sub, coeff_sub, coeff_mul_X_zero, coeff_mul_C, zero_sub]
    have hcs : ∀ a : ℕ, (M * (X - C α)).coeff (a + 1) = M.coeff a - M.coeff (a + 1) * α := fun a =>
      coeff_mul_X_sub_C
    have hbound : ∀ a, v (M.coeff a * α) ≤ 1 := fun a => by
      rw [map_mul]; exact mul_le_one' (ih1 a) hα
    rw [hprod]
    intro i
    rcases i with _ | a
    · rw [hc0, Valuation.map_neg]; exact hbound 0
    · rw [hcs]; exact (Valuation.map_sub _ _ _).trans (max_le (ih1 a) (hbound _))

theorem prod_X_sub_C_coeff_of_one_lt (s : Multiset K) (hs : ∀ α ∈ s, 1 < v α) :
    ((s.map fun α => X - C α).prod).coeff 0 ≠ 0 ∧
      ∀ i, 0 < i → v (((s.map fun α => X - C α).prod).coeff i) < v (((s.map fun α => X - C α).prod).coeff 0) := by
  induction s using Multiset.induction_on with
  | empty =>
    refine ⟨by simp, fun i hi => ?_⟩
    rw [Multiset.map_zero, Multiset.prod_zero, coeff_one, coeff_one, if_neg hi.ne', if_pos rfl, map_zero, map_one]
    exact zero_lt_one
  | cons α s ih =>
    have hα : 1 < v α := hs α (Multiset.mem_cons_self _ _)
    have hα0 : v α ≠ 0 := (zero_lt_one.trans hα).ne'
    obtain ⟨ih1, ih2⟩ := ih fun β hβ => hs β (Multiset.mem_cons_of_mem hβ)
    set M := (s.map fun α => X - C α).prod with hM
    have hprod : ((α ::ₘ s).map fun α => X - C α).prod = M * (X - C α) := by
      rw [Multiset.map_cons, Multiset.prod_cons, mul_comm]
    have hc0 : (M * (X - C α)).coeff 0 = -(M.coeff 0 * α) := by
      rw [mul_sub, coeff_sub, coeff_mul_X_zero, coeff_mul_C, zero_sub]
    have hcs : ∀ a : ℕ, (M * (X - C α)).coeff (a + 1) = M.coeff a - M.coeff (a + 1) * α := fun a =>
      coeff_mul_X_sub_C
    have hM0 : 0 < v (M.coeff 0) := (Valuation.pos_iff _).2 ih1
    have hle : ∀ a, v (M.coeff a) ≤ v (M.coeff 0) := fun a => by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · exact le_rfl
      · exact (ih2 a ha).le
    rw [hprod]
    refine ⟨?_, fun i hi => ?_⟩
    · rw [hc0, neg_ne_zero]
      exact mul_ne_zero ih1 fun h => hα0 (by rw [h, map_zero])
    · obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
      rw [hcs, hc0, Valuation.map_neg, map_mul]
      refine (Valuation.map_sub _ _ _).trans_lt (max_lt ?_ ?_)
      · calc v (M.coeff a) ≤ v (M.coeff 0) := hle a
          _ = v (M.coeff 0) * 1 := (mul_one _).symm
          _ < v (M.coeff 0) * v α := mul_lt_mul_of_pos_left hα hM0
      · rw [map_mul]
        exact mul_lt_mul_of_pos_right (ih2 _ (Nat.succ_pos a)) (zero_lt_one.trans hα)

section AlgClosed

variable [IsAlgClosed K]

theorem natDegree_eq_card_roots' (Q : K[X]) : Q.natDegree = Multiset.card Q.roots :=
  (IsAlgClosed.splits Q).natDegree_eq_card_roots

theorem gauss_eq_lc_of_roots (Q : K[X]) (h : ∀ α ∈ Q.roots, v α ≤ 1) : gauss Q = v Q.leadingCoeff := by
  rw [gauss_eq_prod_roots]
  have : (Q.roots.map fun α => max 1 (v α)) = Q.roots.map fun _ => (1 : Γ₀) :=
    Multiset.map_congr rfl fun α hα => max_eq_left (h α hα)
  rw [this, Multiset.map_const', Multiset.prod_replicate, one_pow, mul_one]

theorem coeff_lt_lc_of_roots (Q : K[X]) (h : ∀ α ∈ Q.roots, v α < 1) :
    ∀ j < Q.natDegree, v (Q.coeff j) < v Q.leadingCoeff := fun j hj => by
  have hQ : Q ≠ 0 := by rintro rfl; simp at hj
  conv_lhs => rw [eq_C_mul_prod Q, coeff_C_mul]
  rw [map_mul]
  have h2 := (prod_X_sub_C_coeff_of_lt_one Q.roots h).2 j (natDegree_eq_card_roots' Q ▸ hj)
  calc v Q.leadingCoeff * v (((Q.roots.map fun α => X - C α).prod).coeff j) < v Q.leadingCoeff * 1 :=
        mul_lt_mul_of_pos_left h2 ((Valuation.pos_iff _).2 (leadingCoeff_ne_zero.2 hQ))
    _ = _ := mul_one _

theorem coeff_le_lc_of_roots (Q : K[X]) (h : ∀ α ∈ Q.roots, v α ≤ 1) :
    ∀ j, v (Q.coeff j) ≤ v Q.leadingCoeff := fun j =>
  (v_coeff_le_gauss Q j).trans (gauss_eq_lc_of_roots Q h).le

theorem coeff_lt_coeff_zero_of_roots (Q : K[X]) (hQ : Q ≠ 0) (h : ∀ α ∈ Q.roots, 1 < v α) :
    ∀ j, 0 < j → v (Q.coeff j) < v (Q.coeff 0) := fun j hj => by
  obtain ⟨_, h2⟩ := prod_X_sub_C_coeff_of_one_lt Q.roots h
  conv_lhs => rw [eq_C_mul_prod Q, coeff_C_mul]
  conv_rhs => rw [eq_C_mul_prod Q, coeff_C_mul]
  rw [map_mul, map_mul]
  exact mul_lt_mul_of_pos_left (h2 j hj) ((Valuation.pos_iff _).2 (leadingCoeff_ne_zero.2 hQ))

theorem orth_outer (PA QA PB QB : K[X]) (hQB : QB ≠ 0) (hdeg : PA.degree < QA.degree)
    (hA : ∀ α ∈ QA.roots, v α < 1) (hB : ∀ β ∈ QB.roots, 1 ≤ v β) :
    gauss (PA * QB + PB * QA) = max (gauss (PA * QB)) (gauss (PB * QA)) := by
  classical
  rcases lt_trichotomy (gauss (PA * QB)) (gauss (PB * QA)) with h | h | h
  · rw [max_eq_right h.le, add_comm]; exact gauss_add_eq_of_lt h
  swap
  · rw [max_eq_left h.le]; exact gauss_add_eq_of_lt h
  rw [h, max_self]
  by_cases hg : gauss (PB * QA) = 0
  · apply le_antisymm ((gauss_add_le _ _).trans (max_le h.le le_rfl))
    rw [hg]; exact zero_le'

  have hgF : gauss (PA * QB) = gauss PA * gauss QB := gauss_mul _ _
  have hgH : gauss (PB * QA) = gauss PB * gauss QA := gauss_mul _ _
  have hPA : PA ≠ 0 := by rintro rfl; rw [zero_mul, gauss_zero] at h; exact hg h.symm
  have hPB : PB ≠ 0 := by rintro rfl; rw [zero_mul, gauss_zero] at hg; exact hg rfl
  have hdeg' : PA.natDegree < QA.natDegree := natDegree_lt_natDegree hPA hdeg
  let I : Finset ℕ := PA.support.filter fun i => v (PA.coeff i) = gauss PA
  have hI : I.Nonempty := by
    obtain ⟨i, hi, hh⟩ := exists_eq_gauss hPA
    exact ⟨i, Finset.mem_filter.2 ⟨hi, hh⟩⟩
  set a0 := I.min' hI with ha0
  have ha0I : a0 ∈ I := Finset.min'_mem I hI
  have ha0v : v (PA.coeff a0) = gauss PA := (Finset.mem_filter.1 ha0I).2
  have ha0le : a0 ≤ PA.natDegree := le_natDegree_of_mem_supp _ (Finset.mem_filter.1 ha0I).1
  have hlt_of_lt : ∀ i < a0, v (PA.coeff i) < gauss PA := fun i hi =>
    lt_of_le_of_ne (v_coeff_le_gauss PA i) fun hh => by
      have hiI : i ∈ I := Finset.mem_filter.2 ⟨Polynomial.mem_support_iff.2 fun h0 => by
        rw [h0, map_zero] at hh; exact gauss_ne_zero hPA hh.symm, hh⟩
      exact absurd (Finset.min'_le I i hiI) (by rw [← ha0]; omega)
  have hgpos : 0 < gauss PA * gauss QB := by rw [← hgF, h]; exact zero_lt_iff.2 hg

  have hFa0 : v ((PA * QB).coeff a0) = gauss PA * gauss QB := by
    rw [coeff_mul, Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.HasAntidiagonal.mem_antidiagonal.2 rfl : (a0, 0) ∈ Finset.HasAntidiagonal.antidiagonal a0)]
    have hmain : v (PA.coeff a0 * QB.coeff 0) = gauss PA * gauss QB := by
      rw [map_mul, ha0v, ← gauss_eq_coeff_zero_of_roots QB hB]
    have hrest : v (∑ x ∈ Finset.HasAntidiagonal.antidiagonal a0 \ {(a0, 0)}, PA.coeff x.1 * QB.coeff x.2) <
        gauss PA * gauss QB := by
      refine Valuation.map_sum_lt _ hgpos.ne' fun x hx => ?_
      obtain ⟨hx1, hx2⟩ := Finset.mem_sdiff.1 hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx1
      rw [Finset.mem_singleton] at hx2
      have hx1lt : x.1 < a0 := by
        rcases Nat.lt_or_ge x.1 a0 with hh | hh
        · exact hh
        · exfalso; apply hx2
          have h1 : x.1 = a0 := by omega
          have h2 : x.2 = 0 := by omega
          exact Prod.ext h1 h2
      rw [map_mul]
      calc v (PA.coeff x.1) * v (QB.coeff x.2) ≤ v (PA.coeff x.1) * gauss QB :=
            mul_le_mul' le_rfl (v_coeff_le_gauss _ _)
        _ < gauss PA * gauss QB := mul_lt_mul_of_pos_right (hlt_of_lt _ hx1lt) (gauss_pos hQB)
    rw [Valuation.map_add_eq_of_lt_left _ (hmain.symm ▸ hrest), hmain]

  have hHa0 : v ((PB * QA).coeff a0) < gauss PB * gauss QA := by
    rw [coeff_mul]
    refine Valuation.map_sum_lt _ (hgH ▸ hg) fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have hx2 : x.2 < QA.natDegree := by omega
    rw [map_mul, gauss_eq_lc_of_roots QA fun α hα => (hA α hα).le]
    calc v (PB.coeff x.1) * v (QA.coeff x.2) ≤ gauss PB * v (QA.coeff x.2) :=
          mul_le_mul' (v_coeff_le_gauss _ _) le_rfl
      _ < gauss PB * v QA.leadingCoeff := mul_lt_mul_of_pos_left (coeff_lt_lc_of_roots QA hA _ hx2) (gauss_pos hPB)
  apply le_antisymm ((gauss_add_le _ _).trans (max_le h.le le_rfl))
  have hlt : v ((PB * QA).coeff a0) < v ((PA * QB).coeff a0) := by rw [hFa0, ← hgF, h, hgH]; exact hHa0
  calc gauss (PB * QA) = v ((PA * QB + PB * QA).coeff a0) := by
        rw [coeff_add, Valuation.map_add_eq_of_lt_left _ hlt, hFa0, ← hgF, h]
    _ ≤ gauss (PA * QB + PB * QA) := v_coeff_le_gauss _ _

theorem orth_inner (PA QA PB QB : K[X]) (hQA : QA ≠ 0) (hQB : QB ≠ 0) (hdeg : PA.degree < QA.degree)
    (hA : ∀ α ∈ QA.roots, v α ≤ 1) (hB : ∀ β ∈ QB.roots, 1 < v β) :
    gauss (PA * QB + PB * QA) = max (gauss (PA * QB)) (gauss (PB * QA)) := by
  classical
  rcases lt_trichotomy (gauss (PA * QB)) (gauss (PB * QA)) with h | h | h
  · rw [max_eq_right h.le, add_comm]; exact gauss_add_eq_of_lt h
  swap
  · rw [max_eq_left h.le]; exact gauss_add_eq_of_lt h
  rw [h, max_self]
  by_cases hg : gauss (PB * QA) = 0
  · apply le_antisymm ((gauss_add_le _ _).trans (max_le h.le le_rfl))
    rw [hg]; exact zero_le'
  have hgF : gauss (PA * QB) = gauss PA * gauss QB := gauss_mul _ _
  have hgH : gauss (PB * QA) = gauss PB * gauss QA := gauss_mul _ _
  have hPA : PA ≠ 0 := by rintro rfl; rw [zero_mul, gauss_zero] at h; exact hg h.symm
  have hPB : PB ≠ 0 := by rintro rfl; rw [zero_mul, gauss_zero] at hg; exact hg rfl
  have hdeg' : PA.natDegree < QA.natDegree := natDegree_lt_natDegree hPA hdeg
  set n := QA.natDegree with hn
  let I : Finset ℕ := PB.support.filter fun i => v (PB.coeff i) = gauss PB
  have hI : I.Nonempty := by
    obtain ⟨i, hi, hh⟩ := exists_eq_gauss hPB
    exact ⟨i, Finset.mem_filter.2 ⟨hi, hh⟩⟩
  set b1 := I.max' hI with hb1
  have hb1I : b1 ∈ I := Finset.max'_mem I hI
  have hb1v : v (PB.coeff b1) = gauss PB := (Finset.mem_filter.1 hb1I).2
  have hlt_of_gt : ∀ i, b1 < i → v (PB.coeff i) < gauss PB := fun i hi =>
    lt_of_le_of_ne (v_coeff_le_gauss PB i) fun hh => by
      have hiI : i ∈ I := Finset.mem_filter.2 ⟨Polynomial.mem_support_iff.2 fun h0 => by
        rw [h0, map_zero] at hh; exact gauss_ne_zero hPB hh.symm, hh⟩
      exact absurd (Finset.le_max' I i hiI) (by rw [← hb1]; omega)
  have hgpos : 0 < gauss PB * gauss QA := by rw [← hgH]; exact zero_lt_iff.2 hg
  have hgQA : gauss QA = v QA.leadingCoeff := gauss_eq_lc_of_roots QA hA

  have hHb : v ((PB * QA).coeff (b1 + n)) = gauss PB * gauss QA := by
    rw [coeff_mul, Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.HasAntidiagonal.mem_antidiagonal.2 rfl : (b1, n) ∈ Finset.HasAntidiagonal.antidiagonal (b1 + n))]
    have hmain : v (PB.coeff b1 * QA.coeff n) = gauss PB * gauss QA := by
      rw [map_mul, hb1v, hn, coeff_natDegree, ← hgQA]
    have hrest : v (∑ x ∈ Finset.HasAntidiagonal.antidiagonal (b1 + n) \ {(b1, n)}, PB.coeff x.1 * QA.coeff x.2) <
        gauss PB * gauss QA := by
      refine Valuation.map_sum_lt _ hgpos.ne' fun x hx => ?_
      obtain ⟨hx1, hx2⟩ := Finset.mem_sdiff.1 hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx1
      rw [Finset.mem_singleton] at hx2
      rw [map_mul]
      rcases Nat.lt_or_ge n x.2 with hh | hh
      ·
        have hq : QA.coeff x.2 = 0 := coeff_eq_zero_of_natDegree_lt (by rw [← hn]; exact hh)
        rw [hq, map_zero, mul_zero]; exact hgpos
      · have hx1gt : b1 < x.1 := by
          rcases Nat.lt_or_ge b1 x.1 with hh' | hh'
          · exact hh'
          · exfalso; apply hx2
            have h1 : x.1 = b1 := by omega
            have h2 : x.2 = n := by omega
            exact Prod.ext h1 h2
        calc v (PB.coeff x.1) * v (QA.coeff x.2) ≤ v (PB.coeff x.1) * gauss QA :=
              mul_le_mul' le_rfl (v_coeff_le_gauss _ _)
          _ < gauss PB * gauss QA := mul_lt_mul_of_pos_right (hlt_of_gt _ hx1gt) (gauss_pos hQA)
    rw [Valuation.map_add_eq_of_lt_left _ (hmain.symm ▸ hrest), hmain]

  have hFb : v ((PA * QB).coeff (b1 + n)) < gauss PA * gauss QB := by
    have hgpos' : 0 < gauss PA * gauss QB := by rw [← hgF, h]; exact zero_lt_iff.2 hg
    rw [coeff_mul]
    refine Valuation.map_sum_lt _ hgpos'.ne' fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [map_mul]
    rcases Nat.lt_or_ge PA.natDegree x.1 with hh | hh
    · rw [coeff_eq_zero_of_natDegree_lt hh, map_zero, zero_mul]; exact hgpos'
    · have hx2 : 0 < x.2 := by omega
      calc v (PA.coeff x.1) * v (QB.coeff x.2) ≤ gauss PA * v (QB.coeff x.2) :=
            mul_le_mul' (v_coeff_le_gauss _ _) le_rfl
        _ < gauss PA * v (QB.coeff 0) :=
            mul_lt_mul_of_pos_left (coeff_lt_coeff_zero_of_roots QB hQB hB _ hx2) (gauss_pos hPA)
        _ = gauss PA * gauss QB := by rw [gauss_eq_coeff_zero_of_roots QB fun β hβ => (hB β hβ).le]
  apply le_antisymm ((gauss_add_le _ _).trans (max_le h.le le_rfl))
  have hlt : v ((PA * QB).coeff (b1 + n)) < v ((PB * QA).coeff (b1 + n)) := by
    rw [hHb, ← hgH, ← h, hgF]; exact hFb
  calc gauss (PB * QA) = v ((PA * QB + PB * QA).coeff (b1 + n)) := by
        rw [coeff_add, Valuation.map_add_eq_of_lt_right _ hlt, hHb, hgH]
    _ ≤ gauss (PA * QB + PB * QA) := v_coeff_le_gauss _ _

end AlgClosed

end IdOrth

end

theorem solution
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (PA QA PB QB : Polynomial K) (hQA : QA ≠ 0) (hQB : QB ≠ 0) (hdeg : PA.degree < QA.degree)
    (h : ((∀ α ∈ QA.roots, Valued.v α < 1) ∧ ∀ β ∈ QB.roots, 1 ≤ Valued.v β) ∨
      ((∀ α ∈ QA.roots, Valued.v α ≤ 1) ∧ ∀ β ∈ QB.roots, 1 < Valued.v β)) :
    (PA * QB + PB * QA).support.sup (fun i => Valued.v ((PA * QB + PB * QA).coeff i)) =
      max ((PA * QB).support.sup fun i => Valued.v ((PA * QB).coeff i))
        ((PB * QA).support.sup fun i => Valued.v ((PB * QA).coeff i)) := by
  rcases h with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · exact IdOrth.orth_outer PA QA PB QB hQB hdeg hA hB
  · exact IdOrth.orth_inner PA QA PB QB hQA hQB hdeg hA hB

end S_CerednikDrinfeld_Omega_gaussNorm_add_eq_max_of_separated_poles
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_gaussNorm_add_eq_max_of_separated_poles (solution)
