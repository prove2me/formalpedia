-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_forall_le_v_apply_of_v_sub_lt_of_forall_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0f03bb29-4ebf-5abc-8b81-ac9fd0a9afa9

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_forall_le_v_apply_of_v_sub_lt_of_forall_ne_zero

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial CerednikDrinfeld.Omega

namespace IdDisc

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

theorem exists_generic (B : Multiset K) : ∃ y : K, v y ≤ 1 ∧ ∀ b ∈ B, v b ≤ 1 → 1 ≤ v (y - b) := by
  classical
  let L : Multiset K := (0 : K) ::ₘ B.filter fun b => v b ≤ 1
  have hL : ∀ b ∈ L, v b ≤ 1 := fun b hb => by
    rcases Multiset.mem_cons.1 hb with rfl | hb
    · rw [map_zero]; exact zero_le'
    · exact (Multiset.mem_filter.1 hb).2
  let F : K[X] := (L.map fun b => X - C b).prod + 1
  have hmonic : (L.map fun b => X - C b).prod.Monic := monic_multiset_prod_of_monic _ _ fun b _ => monic_X_sub_C b
  have hdegprod : (L.map fun b => X - C b).prod.natDegree = Multiset.card L := natDegree_multiset_prod_X_sub_C_eq_card L
  have hcard : 0 < Multiset.card L := Multiset.card_pos.2 (Multiset.cons_ne_zero)
  have hdeg' : (L.map fun b => X - C b).prod.degree = (Multiset.card L : WithBot ℕ) := by
    rw [degree_eq_natDegree hmonic.ne_zero, hdegprod]
  have hFmonic : F.Monic := hmonic.add_of_left (by rw [degree_one, hdeg']; exact_mod_cast hcard)
  have hFdeg : F.degree ≠ 0 := by
    have h1 : F.natDegree = Multiset.card L := by
      rw [show F = (L.map fun b => X - C b).prod + C 1 by rw [C_1], natDegree_add_C, hdegprod]
    rw [degree_eq_natDegree hFmonic.ne_zero, h1]
    exact_mod_cast hcard.ne'
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root F hFdeg
  have hprod : (L.map fun b => y - b).prod = -1 := by
    have h := hy
    rw [IsRoot, eval_add, eval_one, eval_multiset_prod, Multiset.map_map, add_eq_zero_iff_eq_neg] at h
    simpa [Function.comp_def] using h
  have hvprod : (L.map fun b => v (y - b)).prod = 1 := by
    have := congrArg (Valued.v (R := K) (Γ₀ := Γ₀)) hprod
    rwa [map_multiset_prod, Multiset.map_map, Valuation.map_neg, map_one] at this

  have hy1 : v y ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have heq : (L.map fun b => v (y - b)) = L.map fun _ => v y :=
      Multiset.map_congr rfl fun b hb => Valuation.map_sub_eq_of_lt_left _ ((hL b hb).trans_lt hlt)
    rw [heq, Multiset.map_const', Multiset.prod_replicate] at hvprod
    exact absurd hvprod (ne_of_gt (lt_of_lt_of_le hlt (le_self_pow₀ hlt.le hcard.ne')))
  refine ⟨y, hy1, fun b hb hb1 => ?_⟩
  have hbL : b ∈ L := Multiset.mem_cons_of_mem (Multiset.mem_filter.2 ⟨hb, hb1⟩)

  have hle : ∀ b' ∈ L, v (y - b') ≤ 1 := fun b' hb' => (Valuation.map_sub _ _ _).trans (max_le hy1 (hL b' hb'))
  by_contra hlt
  push Not at hlt
  obtain ⟨L', hL'⟩ := Multiset.exists_cons_of_mem hbL
  have hprod_le : ∀ M : Multiset K, (∀ b' ∈ M, v (y - b') ≤ 1) → (M.map fun b' => v (y - b')).prod ≤ 1 := by
    intro M
    induction M using Multiset.induction_on with
    | empty => intro; simp
    | cons a M ih =>
      intro h
      rw [Multiset.map_cons, Multiset.prod_cons]
      exact mul_le_one' (h a (Multiset.mem_cons_self _ _)) (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))
  have hrest : (L'.map fun b' => v (y - b')).prod ≤ 1 :=
    hprod_le L' fun b' hb' => hle b' (hL' ▸ Multiset.mem_cons_of_mem hb')
  rw [hL', Multiset.map_cons, Multiset.prod_cons] at hvprod
  have : v (y - b) * (L'.map fun b' => v (y - b')).prod < 1 :=
    calc _ ≤ v (y - b) * 1 := mul_le_mul' le_rfl hrest
      _ < 1 := by rw [mul_one]; exact hlt
  exact absurd hvprod this.ne

end AlgClosed

end IdDisc

namespace IdDisc

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

def T (P Q : K[X]) : PowerSeries K := (P : PowerSeries K) * (Q : PowerSeries K)⁻¹

theorem constantCoeff_coe_ne_zero {Q : K[X]} (h : Q.coeff 0 ≠ 0) :
    PowerSeries.constantCoeff (Q : PowerSeries K) ≠ 0 := by
  rwa [Polynomial.constantCoeff_coe]

theorem T_mul_coe (P Q : K[X]) (h : Q.coeff 0 ≠ 0) : T P Q * (Q : PowerSeries K) = P := by
  rw [T, mul_assoc, PowerSeries.inv_mul_cancel _ (constantCoeff_coe_ne_zero h), mul_one]

theorem T_zero (Q : K[X]) : T 0 Q = 0 := by rw [T, Polynomial.coe_zero, zero_mul]

theorem T_sub (P₁ Q₁ P₂ Q₂ : K[X]) (h₁ : Q₁.coeff 0 ≠ 0) (h₂ : Q₂.coeff 0 ≠ 0) :
    T (P₁ * Q₂ - P₂ * Q₁) (Q₁ * Q₂) = T P₁ Q₁ - T P₂ Q₂ := by
  have hQ : ((Q₁ * Q₂ : K[X]) : PowerSeries K) ≠ 0 := by
    rw [Ne, Polynomial.coe_eq_zero_iff]
    exact mul_ne_zero (fun h => h₁ (by rw [h, coeff_zero])) (fun h => h₂ (by rw [h, coeff_zero]))
  have h12 : (Q₁ * Q₂).coeff 0 ≠ 0 := by rw [mul_coeff_zero]; exact mul_ne_zero h₁ h₂
  apply mul_right_cancel₀ hQ
  rw [T_mul_coe _ _ h12, sub_mul, Polynomial.coe_mul, ← mul_assoc, T_mul_coe _ _ h₁, mul_comm (Q₁ : PowerSeries K),
    ← mul_assoc, T_mul_coe _ _ h₂, Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_mul]

theorem v_coeff_inv_le (Q : K[X]) (h0 : Q.coeff 0 ≠ 0) (hQ : ∀ i, v (Q.coeff i) ≤ v (Q.coeff 0)) (n : ℕ) :
    v (PowerSeries.coeff n (Q : PowerSeries K)⁻¹) ≤ (v (Q.coeff 0))⁻¹ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_inv, Polynomial.constantCoeff_coe]
    have hv0 : v (Q.coeff 0) ≠ 0 := by rwa [Ne, map_eq_zero]
    split_ifs with hn
    · rw [map_inv₀]
    · rw [Valuation.map_mul, Valuation.map_neg, map_inv₀]
      refine mul_le_of_le_one_right' (Valuation.map_sum_le _ fun x hx => ?_)
      split_ifs with hx2
      · rw [Valuation.map_mul, Polynomial.coeff_coe]
        calc v (Q.coeff x.1) * v (PowerSeries.coeff x.2 (Q : PowerSeries K)⁻¹)
            ≤ v (Q.coeff 0) * (v (Q.coeff 0))⁻¹ := mul_le_mul' (hQ _) (ih _ hx2)
          _ = 1 := mul_inv_cancel₀ hv0
      · rw [map_zero]; exact zero_le'

theorem v_coeff_T_le (P Q : K[X]) (h0 : Q.coeff 0 ≠ 0) (hQ : ∀ i, v (Q.coeff i) ≤ v (Q.coeff 0)) (m : ℕ) :
    v (PowerSeries.coeff m (T P Q)) ≤ gauss P * (v (Q.coeff 0))⁻¹ := by
  rw [T, PowerSeries.coeff_mul]
  refine Valuation.map_sum_le _ fun x _ => ?_
  rw [Valuation.map_mul, Polynomial.coeff_coe]
  exact mul_le_mul' (v_coeff_le_gauss P _) (v_coeff_inv_le Q h0 hQ _)

theorem gauss_lt_of_coeff_T_lt (P Q : K[X]) (h0 : Q.coeff 0 ≠ 0) (hQ0 : Q ≠ 0) {γ : Γ₀} (hγ : γ ≠ 0)
    (h : ∀ m, v (PowerSeries.coeff m (T P Q)) < γ) : gauss P < γ * gauss Q := by
  refine gauss_lt (mul_ne_zero hγ (gauss_ne_zero hQ0)) fun i => ?_
  have hi : P.coeff i = PowerSeries.coeff i (T P Q * (Q : PowerSeries K)) := by
    rw [T_mul_coe _ _ h0, Polynomial.coeff_coe]
  rw [hi, PowerSeries.coeff_mul]
  refine Valuation.map_sum_lt _ (mul_ne_zero hγ (gauss_ne_zero hQ0)) fun x _ => ?_
  rw [Valuation.map_mul, Polynomial.coeff_coe]
  calc v (PowerSeries.coeff x.1 (T P Q)) * v (Q.coeff x.2) ≤ v (PowerSeries.coeff x.1 (T P Q)) * gauss Q :=
        mul_le_mul' le_rfl (v_coeff_le_gauss Q _)
    _ < γ * gauss Q := mul_lt_mul_of_pos_right (h _) (gauss_pos hQ0)

theorem coe_comp_C_mul_X (P : K[X]) (δ : K) : ((P.comp (C δ * X) : K[X]) : PowerSeries K) = PowerSeries.rescale δ P := by
  ext n
  rw [Polynomial.coeff_coe, comp_C_mul_X_coeff, PowerSeries.coeff_rescale, Polynomial.coeff_coe, mul_comm]

theorem T_comp_C_mul_X (P Q : K[X]) (δ : K) (h0 : Q.coeff 0 ≠ 0) (m : ℕ) :
    PowerSeries.coeff m (T (P.comp (C δ * X)) (Q.comp (C δ * X))) = PowerSeries.coeff m (T P Q) * δ ^ m := by
  have hinv : (PowerSeries.rescale δ (Q : PowerSeries K))⁻¹ = PowerSeries.rescale δ (Q : PowerSeries K)⁻¹ := by
    symm
    rw [PowerSeries.eq_inv_iff_mul_eq_one, ← map_mul, PowerSeries.inv_mul_cancel _ (constantCoeff_coe_ne_zero h0),
      map_one]
    rwa [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.constantCoeff_coe]
  rw [T, T, coe_comp_C_mul_X, coe_comp_C_mul_X, hinv, ← map_mul, PowerSeries.coeff_rescale, mul_comm]

def aff (c π : K) (r : RatPair K) : RatPair K := ⟨r.num.comp (C π * X + C c), r.den.comp (C π * X + C c)⟩

theorem aff_den_eval (c π : K) (r : RatPair K) (y : K) : (aff c π r).den.eval y = r.den.eval (π * y + c) := by
  simp [aff, eval_comp]

theorem aff_num_eval (c π : K) (r : RatPair K) (y : K) : (aff c π r).num.eval y = r.num.eval (π * y + c) := by
  simp [aff, eval_comp]

theorem aff_evalAt (c π : K) (r : RatPair K) (y : K) : (aff c π r).evalAt y = r.evalAt (π * y + c) := by
  rw [RatPair.evalAt, RatPair.evalAt, aff_den_eval, aff_num_eval]
end IdDisc

namespace IdDisc

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

end AlgClosed

end IdDisc

namespace IdDisc

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

section NewtonPolygon

variable [IsAlgClosed K]

open scoped Classical

def rin (B : K[X]) : Multiset K := B.roots.filter fun α => v α ≤ 1
def rout (B : K[X]) : Multiset K := B.roots.filter fun α => ¬ v α ≤ 1

def Bin (B : K[X]) : K[X] := ((rin B).map fun α => X - C α).prod
def Bout (B : K[X]) : K[X] := ((rout B).map fun α => X - C α).prod

theorem Bin_monic (B : K[X]) : (Bin B).Monic := monic_multiset_prod_of_monic _ _ fun α _ => monic_X_sub_C α
theorem Bout_monic (B : K[X]) : (Bout B).Monic := monic_multiset_prod_of_monic _ _ fun α _ => monic_X_sub_C α

theorem roots_Bin (B : K[X]) : (Bin B).roots = rin B := roots_multiset_prod_X_sub_C _
theorem roots_Bout (B : K[X]) : (Bout B).roots = rout B := roots_multiset_prod_X_sub_C _

theorem natDegree_Bin (B : K[X]) : (Bin B).natDegree = (rin B).card := by
  simp only [Bin, natDegree_multiset_prod_X_sub_C_eq_card]

theorem eq_C_mul_Bin_mul_Bout (B : K[X]) : B = C B.leadingCoeff * (Bin B * Bout B) := by
  conv_lhs => rw [eq_C_mul_prod B]
  rw [Bin, Bout, ← Multiset.prod_add, ← Multiset.map_add, rin, rout, Multiset.filter_add_not]

theorem gauss_Bin (B : K[X]) : gauss (Bin B) = 1 := by
  rw [gauss_eq_lc_of_roots (Bin B) (fun α hα => by rw [roots_Bin] at hα; exact (Multiset.mem_filter.1 hα).2),
    (Bin_monic B).leadingCoeff, map_one]

theorem gauss_Bout (B : K[X]) : gauss (Bout B) = v ((Bout B).coeff 0) :=
  gauss_eq_coeff_zero_of_roots _ fun α hα => by
    rw [roots_Bout] at hα; exact (not_le.1 (Multiset.mem_filter.1 hα).2).le

theorem coeff_Bout_lt (B : K[X]) {i : ℕ} (hi : 0 < i) : v ((Bout B).coeff i) < v ((Bout B).coeff 0) :=
  coeff_lt_coeff_zero_of_roots _ (Bout_monic B).ne_zero
    (fun α hα => by rw [roots_Bout] at hα; exact not_le.1 (Multiset.mem_filter.1 hα).2) i hi

theorem Bout_coeff_zero_ne (B : K[X]) : (Bout B).coeff 0 ≠ 0 := by
  rw [coeff_zero_eq_eval_zero]
  intro h0
  have : (0 : K) ∈ (Bout B).roots := (mem_roots (Bout_monic B).ne_zero).2 h0
  rw [roots_Bout] at this
  exact (Multiset.mem_filter.1 this).2 (by rw [map_zero]; exact zero_le')

theorem v_coeff_card_rin_eq_gauss (B : K[X]) (hB : B ≠ 0) : v (B.coeff (rin B).card) = gauss B := by
  set m := (rin B).card with hm
  have hdeg : (Bin B).natDegree = m := natDegree_Bin B
  have key : v ((Bin B * Bout B).coeff m) = gauss (Bin B) * gauss (Bout B) := by
    rw [coeff_mul]
    have hmem : (m, 0) ∈ Finset.HasAntidiagonal.antidiagonal m := by simp
    rw [← Finset.add_sum_erase _ _ hmem]
    have hmain : v ((Bin B).coeff m * (Bout B).coeff 0) = gauss (Bin B) * gauss (Bout B) := by
      rw [map_mul, ← hdeg, coeff_natDegree, (Bin_monic B).leadingCoeff, map_one, gauss_Bin, gauss_Bout]
    have hrest : v (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal m).erase (m, 0), (Bin B).coeff x.1 * (Bout B).coeff x.2)
        < gauss (Bin B) * gauss (Bout B) := by
      apply Valuation.map_sum_lt
      · rw [gauss_Bin, one_mul, gauss_Bout]
        exact (Valuation.ne_zero_iff _).2 (Bout_coeff_zero_ne B)
      · intro x hx
        obtain ⟨hx1, hx2⟩ := Finset.mem_erase.1 hx
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx2
        have hx2pos : 0 < x.2 := by
          rcases Nat.eq_zero_or_pos x.2 with h | h
          · exfalso; apply hx1
            have h1 : x.1 = m := by omega
            exact Prod.ext h1 h
          · exact h
        rw [map_mul, gauss_Bin, one_mul, gauss_Bout]
        calc v ((Bin B).coeff x.1) * v ((Bout B).coeff x.2)
            ≤ 1 * v ((Bout B).coeff x.2) := by
              apply mul_le_mul_left
              exact (v_coeff_le_gauss _ _).trans (gauss_Bin B).le
          _ < v ((Bout B).coeff 0) := by rw [one_mul]; exact coeff_Bout_lt B hx2pos
    rw [Valuation.map_add_eq_of_lt_left _ (by rw [hmain]; exact hrest), hmain]
  have hfac := eq_C_mul_Bin_mul_Bout B
  have hcoeff : B.coeff m = B.leadingCoeff * (Bin B * Bout B).coeff m := by
    conv_lhs => rw [hfac]
    rw [coeff_C_mul]
  rw [hcoeff, map_mul, key, ← gauss_mul, ← gauss_C_mul, ← hfac]

theorem card_rin_le (B : K[X]) (hB : B ≠ 0) (n : ℕ) (hdom : ∀ j, n < j → v (B.coeff j) < v (B.coeff n)) :
    (rin B).card ≤ n := by
  by_contra hlt
  push Not at hlt
  have h1 := hdom _ hlt
  rw [v_coeff_card_rin_eq_gauss B hB] at h1
  exact (not_lt.2 (v_coeff_le_gauss B n)) h1

end NewtonPolygon

end IdDisc

namespace IdDisc

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

section Dominant

theorem coeff_eq_sum_T (P Q : K[X]) (h0 : Q.coeff 0 ≠ 0) (j : ℕ) :
    P.coeff j = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal j, PowerSeries.coeff x.1 (T P Q) * Q.coeff x.2 := by
  have := congrArg (PowerSeries.coeff j) (T_mul_coe P Q h0)
  rw [Polynomial.coeff_coe] at this
  rw [← this, PowerSeries.coeff_mul]
  simp only [Polynomial.coeff_coe]

theorem coeff_dominant_of_T (P Q : K[X]) (h0 : Q.coeff 0 ≠ 0)
    (hQ : ∀ i, 0 < i → v (Q.coeff i) < v (Q.coeff 0)) (n : ℕ)
    (hpos : 0 < v (PowerSeries.coeff n (T P Q)))
    (hle : ∀ i, v (PowerSeries.coeff i (T P Q)) ≤ v (PowerSeries.coeff n (T P Q)))
    (hlt : ∀ j, n < j → v (PowerSeries.coeff j (T P Q)) < v (PowerSeries.coeff n (T P Q))) :
    v (P.coeff n) = v (PowerSeries.coeff n (T P Q)) * v (Q.coeff 0) ∧
      ∀ j, n < j → v (P.coeff j) < v (PowerSeries.coeff n (T P Q)) * v (Q.coeff 0) := by
  set cn := PowerSeries.coeff n (T P Q) with hcn
  have hq0 : 0 < v (Q.coeff 0) := (Valuation.pos_iff _).2 h0
  have hterm : ∀ j, n ≤ j → ∀ x ∈ Finset.HasAntidiagonal.antidiagonal j, x ≠ (n, 0) →
      v (PowerSeries.coeff x.1 (T P Q) * Q.coeff x.2) < v cn * v (Q.coeff 0) := by
    intro j hnj x hx hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [map_mul]
    rcases lt_trichotomy x.1 n with h1 | h1 | h1
    · have hx2 : 0 < x.2 := by omega
      calc v (PowerSeries.coeff x.1 (T P Q)) * v (Q.coeff x.2) ≤ v cn * v (Q.coeff x.2) :=
            mul_le_mul_left (hle _) _
        _ < v cn * v (Q.coeff 0) := mul_lt_mul_of_pos_left (hQ _ hx2) hpos
    · have hx2 : 0 < x.2 := by
        rcases Nat.eq_zero_or_pos x.2 with h2 | h2
        · exfalso; apply hne; exact Prod.ext h1 h2
        · exact h2
      rw [h1]
      exact mul_lt_mul_of_pos_left (hQ _ hx2) hpos
    · have hq : v (Q.coeff x.2) ≤ v (Q.coeff 0) := by
        rcases Nat.eq_zero_or_pos x.2 with h2 | h2
        · rw [h2]
        · exact (hQ _ h2).le
      calc v (PowerSeries.coeff x.1 (T P Q)) * v (Q.coeff x.2)
          ≤ v (PowerSeries.coeff x.1 (T P Q)) * v (Q.coeff 0) := mul_le_mul_right hq _
        _ < v cn * v (Q.coeff 0) := mul_lt_mul_of_pos_right (hlt _ h1) hq0
  constructor
  · rw [coeff_eq_sum_T P Q h0 n]
    have hmem : (n, 0) ∈ Finset.HasAntidiagonal.antidiagonal n := by simp
    rw [← Finset.add_sum_erase _ _ hmem]
    have hmain : v (PowerSeries.coeff n (T P Q) * Q.coeff 0) = v cn * v (Q.coeff 0) := by rw [map_mul]
    have hrest : v (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (n, 0), PowerSeries.coeff x.1 (T P Q) * Q.coeff x.2)
        < v cn * v (Q.coeff 0) :=
      Valuation.map_sum_lt _ (mul_ne_zero hpos.ne' hq0.ne') fun x hx =>
        hterm n le_rfl x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx)
    rw [Valuation.map_add_eq_of_lt_left _ (by rw [hmain]; exact hrest), hmain]
  · intro j hj
    rw [coeff_eq_sum_T P Q h0 j]
    refine Valuation.map_sum_lt _ (mul_ne_zero hpos.ne' hq0.ne') fun x hx => hterm j hj.le x hx ?_
    rintro rfl
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    simp at hx; omega

end Dominant

section Perturb

variable [IsAlgClosed K]

open scoped Classical

theorem card_rin_sub_le (P E : K[X]) (n : ℕ) {M : Γ₀} (hPn : v (P.coeff n) = M)
    (hPgt : ∀ j, n < j → v (P.coeff j) < M) (hE : ∀ j, v (E.coeff j) < M) :
    P - E ≠ 0 ∧ (rin (P - E)).card ≤ n := by
  have hM : M ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' (hE 0))
  have hn : v ((P - E).coeff n) = M := by
    rw [coeff_sub, Valuation.map_sub_eq_of_lt_left _ (by rw [hPn]; exact hE n), hPn]
  have hne : P - E ≠ 0 := fun h => by
    rw [h, coeff_zero, map_zero] at hn; exact hM hn.symm
  refine ⟨hne, card_rin_le _ hne n fun j hj => ?_⟩
  rw [hn, coeff_sub]
  exact (Valuation.map_sub _ _ _).trans_lt (max_lt (hPgt j hj) (hE j))

theorem gauss_finset_prod {ι : Type} (s : Finset ι) (f : ι → K[X]) :
    gauss (∏ i ∈ s, f i) = ∏ i ∈ s, gauss (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gauss_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, gauss_mul, ih]

theorem gauss_lagrange_basis (s : Finset K) (hs : ∀ z ∈ s, v z ≤ 1) (i : K) (hi : i ∈ s) :
    gauss (Lagrange.basis s id i) = (v (∏ j ∈ s.erase i, (i - j)))⁻¹ := by
  rw [show Lagrange.basis s id i = ∏ j ∈ s.erase i, Lagrange.basisDivisor (id i) (id j) from rfl,
    gauss_finset_prod, map_prod, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hji : j ∈ s := Finset.mem_of_mem_erase hj
  rw [Lagrange.basisDivisor, gauss_C_mul, id, id, ← one_mul (X - C j), gauss_mul_X_sub_C, gauss_one, one_mul,
    max_eq_left (hs j hji), mul_one, map_inv₀]

theorem v_coeff_interpolate_lt (s : Finset K) (hs : ∀ z ∈ s, v z ≤ 1) (r : K → K) {M : Γ₀} (hM : M ≠ 0)
    (hr : ∀ i ∈ s, v (r i) < M * v (∏ j ∈ s.erase i, (i - j))) (m : ℕ) :
    v ((Lagrange.interpolate s id r).coeff m) < M := by
  rw [Lagrange.interpolate_apply, finset_sum_coeff]
  refine Valuation.map_sum_lt _ hM fun i hi => ?_
  rw [coeff_C_mul, map_mul]
  have hprod : v (∏ j ∈ s.erase i, (i - j)) ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun j hj =>
      (Valuation.ne_zero_iff _).2 (sub_ne_zero.2 (Finset.ne_of_mem_erase hj).symm)
  calc v (r i) * v ((Lagrange.basis s id i).coeff m) ≤ v (r i) * gauss (Lagrange.basis s id i) :=
        mul_le_mul_right (v_coeff_le_gauss _ _) _
    _ = v (r i) * (v (∏ j ∈ s.erase i, (i - j)))⁻¹ := by rw [gauss_lagrange_basis s hs i hi]
    _ < M := by rw [mul_inv_lt_iff₀ (zero_lt_iff.2 hprod)]; exact hr i hi

end Perturb

end IdDisc

namespace IdDisc

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

theorem unif_eps {α : Type} {F : ℕ → α → K} {φ : α → K} (h : TendstoUniformly F φ Filter.atTop) :
    ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z, v (F k z - φ z) < v e := fun e he => by
  rw [tendstoUniformly_iff_vRestrict] at h
  have hwe : vRestrict K e ≠ 0 := by rwa [ne_eq, map_eq_zero]
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h (Units.mk0 _ hwe))
  exact ⟨N, fun k hk z => (v_lt_iff_vRestrict_lt K _ _).2 (hN k hk z)⟩

section ZC0

variable [IsAlgClosed K]

open scoped Classical

theorem zc0 (S : Set K) (Z : Finset K) (hZ : ∀ ζ ∈ Z, v ζ = 1)
    (hS : ∀ y : K, v y ≤ 1 → (∀ ζ ∈ Z, 1 ≤ v (y - ζ)) → y ∈ S)
    {f : ↥S → K} (hf : f ∈ holOn K S) :
    (∀ y : ↥S, v (y : K) ≤ 1 → (∀ ζ ∈ Z, 1 ≤ v ((y : K) - ζ)) → f y = 0) ∨
      Set.Finite {y : ↥S | v (y : K) < 1 ∧ f y = 0} := by
  obtain ⟨r, hpf, -, hlim⟩ := hf
  have hung := unif_eps hlim

  have hS' : ∀ y : K, v y < 1 → y ∈ S := fun y hy => hS y hy.le fun ζ hζ => by
    rw [Valuation.map_sub_eq_of_lt_right _ (by rw [hZ ζ hζ]; exact hy), hZ ζ hζ]
  have hden0 : ∀ k, (r k).den.eval 0 ≠ 0 := fun k => hpf k 0 (hS' 0 (by rw [map_zero]; exact zero_lt_one))
  have hcoef0 : ∀ k, (r k).den.coeff 0 ≠ 0 := fun k => by rw [coeff_zero_eq_eval_zero]; exact hden0 k
  have hden_ne : ∀ k, (r k).den ≠ 0 := fun k h => hcoef0 k (by rw [h, coeff_zero])
  have hroots : ∀ k, ∀ α ∈ (r k).den.roots, 1 ≤ v α := fun k α hα => by
    by_contra hlt
    push Not at hlt
    exact hpf k α (hS' α hlt) ((mem_roots (hden_ne k)).1 hα)
  have hrootsZ : ∀ k (y : K), v y ≤ 1 → (∀ ζ ∈ Z, 1 ≤ v (y - ζ)) →
      ∀ α ∈ (r k).den.roots, v α ≤ 1 → 1 ≤ v (y - α) := by
    intro k y _ hyZ α hα hα1
    by_contra hlt
    push Not at hlt
    refine hpf k α (hS α hα1 fun ζ hζ => ?_) ((mem_roots (hden_ne k)).1 hα)
    have : α - ζ = (y - ζ) - (y - α) := by ring
    rw [this, Valuation.map_sub_eq_of_lt_left _ (hlt.trans_le (hyZ ζ hζ))]
    exact hyZ ζ hζ
  have hgQ : ∀ k, gauss (r k).den = v ((r k).den.coeff 0) := fun k =>
    gauss_eq_coeff_zero_of_roots _ (hroots k)
  have hQcoef : ∀ k i, v ((r k).den.coeff i) ≤ v ((r k).den.coeff 0) := fun k i =>
    (hgQ k) ▸ v_coeff_le_gauss _ i
  have hgQpos : ∀ k, 0 < gauss (r k).den := fun k => gauss_pos (hden_ne k)

  have hC : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ y ∈ S,
      v ((r k).evalAt y - (r j).evalAt y) < v e := fun e he => by
    obtain ⟨N, hN⟩ := hung e he
    refine ⟨N, fun k hk j hj y hy => ?_⟩
    have : (r k).evalAt y - (r j).evalAt y = ((r k).evalAt y - f ⟨y, hy⟩) - ((r j).evalAt y - f ⟨y, hy⟩) := by
      ring
    rw [this]
    exact Valuation.map_sub_lt _ (hN k hk ⟨y, hy⟩) (hN j hj ⟨y, hy⟩)

  have hvalF : ∀ k (y : K), v y ≤ 1 → (∀ ζ ∈ Z, 1 ≤ v (y - ζ)) →
      v ((r k).evalAt y) ≤ gauss (r k).num / gauss (r k).den := by
    intro k y hy1 hyZ
    have hQy : v ((r k).den.eval y) = gauss (r k).den := v_eval_eq_gauss _ hy1 (hrootsZ k y hy1 hyZ)
    show v ((r k).num.eval y / (r k).den.eval y) ≤ _
    rw [map_div₀, hQy]
    exact div_le_div_of_nonneg_right (v_eval_le_gauss _ hy1) (hgQpos k).le

  have hvalgen : ∀ k (y : K), v y ≤ 1 → (∀ b ∈ (r k).num.roots + (r k).den.roots, v b ≤ 1 → 1 ≤ v (y - b)) →
      v ((r k).evalAt y) = gauss (r k).num / gauss (r k).den := by
    intro k y hy1 hgen
    show v ((r k).num.eval y / (r k).den.eval y) = _
    rw [map_div₀, v_eval_eq_gauss _ hy1 (fun α hα => hgen α (Multiset.mem_add.2 (Or.inl hα))),
      v_eval_eq_gauss _ hy1 (fun α hα => hgen α (Multiset.mem_add.2 (Or.inr hα)))]

  by_cases hI : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, gauss (r k).num / gauss (r k).den < v e
  · left
    intro y hy1 hyZ
    by_contra hfy
    obtain ⟨N₁, hN₁⟩ := hI (f y) hfy
    obtain ⟨N₂, hN₂⟩ := hung (f y) hfy
    set k := max N₁ N₂
    have h1 : v ((r k).evalAt y) < v (f y) := (hvalF k y hy1 hyZ).trans_lt (hN₁ k (le_max_left _ _))
    have h2 : v ((r k).evalAt y - f y) < v (f y) := hN₂ k (le_max_right _ _) y
    have : f y = (r k).evalAt y - ((r k).evalAt y - f y) := by ring
    have h3 : v (f y) < v (f y) := by
      conv_lhs => rw [this]
      exact Valuation.map_sub_lt _ h1 h2
    exact lt_irrefl _ h3

  right
  push Not at hI
  obtain ⟨e₀, he₀, hfreq⟩ := hI

  obtain ⟨N₀, hN₀⟩ := hC e₀ he₀

  let c : ℕ → ℕ → K := fun k m => PowerSeries.coeff m (T (r k).num (r k).den)
  have hZ' : ∀ ζ ∈ Z, 1 ≤ v ζ := fun ζ hζ => (hZ ζ hζ).ge
  have hA : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ m, v (c k m - c j m) < v e := by
    intro e he
    obtain ⟨N, hN⟩ := hC e he
    refine ⟨N, fun k hk j hj m => ?_⟩
    set P := (r k).num * (r j).den - (r j).num * (r k).den with hP
    set Q := (r k).den * (r j).den with hQ
    have hQ0 : Q.coeff 0 ≠ 0 := by rw [hQ, mul_coeff_zero]; exact mul_ne_zero (hcoef0 k) (hcoef0 j)
    have hQne : Q ≠ 0 := mul_ne_zero (hden_ne k) (hden_ne j)
    have hbT : c k m - c j m = PowerSeries.coeff m (T P Q) := by
      simp only [c]; rw [hP, hQ, T_sub _ _ _ _ (hcoef0 k) (hcoef0 j), map_sub]
    rw [hbT]
    have hQroots : ∀ α ∈ Q.roots, 1 ≤ v α := fun α hα => by
      rw [hQ, roots_mul hQne, Multiset.mem_add] at hα
      rcases hα with hα | hα
      · exact hroots k α hα
      · exact hroots j α hα
    have hgQ' : gauss Q = v (Q.coeff 0) := gauss_eq_coeff_zero_of_roots Q hQroots
    have hQcoef' : ∀ i, v (Q.coeff i) ≤ v (Q.coeff 0) := fun i => hgQ' ▸ v_coeff_le_gauss Q i
    obtain ⟨y, hy1, hygen⟩ := exists_generic (Z.val + P.roots + Q.roots)
    have hyZ : ∀ ζ ∈ Z, 1 ≤ v (y - ζ) := fun ζ hζ => hygen ζ (by simp [hζ]) (hZ ζ hζ).le
    have hyS : y ∈ S := hS y hy1 hyZ
    have hvP : v (P.eval y) = gauss P := v_eval_eq_gauss P hy1 fun α hα => hygen α (by simp [hα])
    have hvQ : v (Q.eval y) = gauss Q := v_eval_eq_gauss Q hy1 fun α hα => hygen α (by simp [hα])
    have hdiff : (r k).evalAt y - (r j).evalAt y = P.eval y / Q.eval y := by
      rw [hP, hQ]
      simp only [RatPair.evalAt, eval_sub, eval_mul]
      rw [div_sub_div _ _ (hpf k y hyS) (hpf j y hyS)]
      congr 1
      ring
    have hlt : gauss P < v e * gauss Q := by
      have := hN k hk j hj y hyS
      rwa [hdiff, map_div₀, hvP, hvQ, div_lt_iff₀ (gauss_pos hQne)] at this
    have hv0 : v (Q.coeff 0) ≠ 0 := by rwa [Ne, map_eq_zero]
    calc v (PowerSeries.coeff m (T P Q)) ≤ gauss P * (v (Q.coeff 0))⁻¹ := v_coeff_T_le P Q hQ0 hQcoef' m
      _ < v e * gauss Q * (v (Q.coeff 0))⁻¹ := mul_lt_mul_of_pos_right hlt (zero_lt_iff.2 (inv_ne_zero hv0))
      _ = v e := by rw [← hgQ', mul_assoc, mul_inv_cancel₀ (gauss_ne_zero hQne), mul_one]
  obtain ⟨N₁, hN₁⟩ := hA e₀ he₀
  obtain ⟨k₀, hk₀, hge⟩ := hfreq (max N₀ N₁)
  have hk₀N₀ : N₀ ≤ k₀ := (le_max_left _ _).trans hk₀
  have hk₀N₁ : N₁ ≤ k₀ := (le_max_right _ _).trans hk₀
  set M₀ : Γ₀ := gauss (r k₀).num / gauss (r k₀).den with hM₀
  have hve₀ : 0 < v e₀ := (Valuation.pos_iff _).2 he₀
  have hM₀pos : 0 < M₀ := hve₀.trans_le hge

  have hstab : ∀ k, N₀ ≤ k → gauss (r k).num / gauss (r k).den = M₀ := by
    intro k hk
    obtain ⟨y, hy1, hygen⟩ :=
      exists_generic (Z.val + ((r k).num.roots + (r k).den.roots) + ((r k₀).num.roots + (r k₀).den.roots))
    have hyZ : ∀ ζ ∈ Z, 1 ≤ v (y - ζ) := fun ζ hζ => hygen ζ (by simp [hζ]) (hZ ζ hζ).le
    have hyS : y ∈ S := hS y hy1 hyZ
    have hk' := hvalgen k y hy1 (fun b hb => hygen b (by
      rw [Multiset.mem_add, Multiset.mem_add]; exact Or.inl (Or.inr hb)))
    have hk₀' := hvalgen k₀ y hy1 (fun b hb => hygen b (by rw [Multiset.mem_add]; exact Or.inr hb))
    rw [← hk', hM₀, ← hk₀']
    have hdiff : v ((r k).evalAt y - (r k₀).evalAt y) < v ((r k₀).evalAt y) := by
      rw [hk₀']; exact (hN₀ k hk k₀ hk₀N₀ y hyS).trans_le hge
    have : (r k).evalAt y = (r k₀).evalAt y + ((r k).evalAt y - (r k₀).evalAt y) := by ring
    rw [this]
    exact Valuation.map_add_eq_of_lt_left _ hdiff

  have hcoefM : ∀ k, N₀ ≤ k → ∀ m, v (c k m) ≤ M₀ := by
    intro k hk m
    calc v (c k m) ≤ gauss (r k).num * (v ((r k).den.coeff 0))⁻¹ := v_coeff_T_le _ _ (hcoef0 k) (hQcoef k) m
      _ = gauss (r k).num / gauss (r k).den := by rw [← hgQ k, div_eq_mul_inv]
      _ = M₀ := hstab k hk

  have hnum0 : (r k₀).num ≠ 0 := by
    intro h
    apply hM₀pos.ne'
    show gauss (r k₀).num / gauss (r k₀).den = 0
    rw [h, gauss_zero, zero_div]
  have hq0pos : ∀ k, 0 < v ((r k).den.coeff 0) := fun k => (Valuation.pos_iff _).2 (hcoef0 k)
  have hD : ∃ ν : ℕ, v (c k₀ ν) = M₀ := by
    by_contra hno
    push Not at hno
    have hlt' : ∀ m, v (c k₀ m) < M₀ := fun m => lt_of_le_of_ne (hcoefM k₀ hk₀N₀ m) (hno m)
    have : gauss (r k₀).num < gauss (r k₀).num := by
      have hM₀q : M₀ * v ((r k₀).den.coeff 0) = gauss (r k₀).num := by
        show gauss (r k₀).num / gauss (r k₀).den * v ((r k₀).den.coeff 0) = gauss (r k₀).num
        rw [← hgQ k₀, div_mul_cancel₀ _ (gauss_ne_zero (hden_ne k₀))]
      refine gauss_lt (gauss_ne_zero hnum0) fun i => ?_
      rw [coeff_eq_sum_T _ _ (hcoef0 k₀) i, ← hM₀q]
      refine Valuation.map_sum_lt _ (mul_ne_zero hM₀pos.ne' (hq0pos k₀).ne') fun x _ => ?_
      rw [map_mul]
      calc v (PowerSeries.coeff x.1 (T (r k₀).num (r k₀).den)) * v ((r k₀).den.coeff x.2)
          ≤ v (c k₀ x.1) * v ((r k₀).den.coeff 0) := mul_le_mul_right (hQcoef k₀ x.2) _
        _ < M₀ * v ((r k₀).den.coeff 0) := mul_lt_mul_of_pos_right (hlt' x.1) (hq0pos k₀)
    exact lt_irrefl _ this
  obtain ⟨ν, hν₀⟩ := hD

  have hν : ∀ k, k₀ ≤ k → v (c k ν) = M₀ := by
    intro k hk
    have hdiff := hN₁ k (hk₀N₁.trans hk) k₀ hk₀N₁ ν
    have : c k ν = c k₀ ν + (c k ν - c k₀ ν) := by ring
    rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [hν₀]; exact hdiff.trans_le hge), hν₀]

  obtain ⟨y₀, hy₀1, hy₀gen⟩ := exists_generic (Z.val + ((r k₀).num.roots + (r k₀).den.roots))
  have hy₀Z : ∀ ζ ∈ Z, 1 ≤ v (y₀ - ζ) := fun ζ hζ => hy₀gen ζ (by simp [hζ]) (hZ ζ hζ).le
  set eM : K := (r k₀).evalAt y₀ with heM
  have hveM : v eM = M₀ := hvalgen k₀ y₀ hy₀1 (fun b hb => hy₀gen b (by rw [Multiset.mem_add]; exact Or.inr hb))
  have heM0 : eM ≠ 0 := (Valuation.ne_zero_iff _).1 (by rw [hveM]; exact hM₀pos.ne')

  by_contra hinf
  obtain ⟨W, hWsub, hWcard⟩ := Set.Infinite.exists_subset_card_eq hinf (ν + 2)
  set s : Finset K := W.image (fun y : ↥S => (y : K)) with hsdef
  have hscard : s.card = ν + 2 := by
    rw [hsdef, Finset.card_image_of_injective _ Subtype.coe_injective, hWcard]
  have hsprop : ∀ z ∈ s, v z < 1 ∧ ∃ hz : z ∈ S, f ⟨z, hz⟩ = 0 := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    have := hWsub hy
    exact ⟨this.1, y.2, this.2⟩
  obtain ⟨t, hts, htmax⟩ := Finset.exists_max_image s (fun z => v z)
    (Finset.card_pos.1 (by rw [hscard]; omega))
  have ht1 : v t < 1 := (hsprop t hts).1
  have ht0 : t ≠ 0 := by
    intro h0
    have hsub : s ⊆ {0} := fun z hz => by
      have := htmax z hz
      rw [h0, map_zero, le_zero_iff] at this
      exact Finset.mem_singleton.2 ((Valuation.zero_iff _).1 this)
    have := Finset.card_le_card hsub
    rw [hscard, Finset.card_singleton] at this
    omega
  have hvt : 0 < v t := (Valuation.pos_iff _).2 ht0

  set s' : Finset K := s.image (fun z => z / t) with hs'def
  have hdivinj : Function.Injective (fun z : K => z / t) := fun a b h => by
    simpa [div_left_inj' ht0] using h
  have hs'card : s'.card = ν + 2 := by rw [hs'def, Finset.card_image_of_injective _ hdivinj, hscard]
  have hs'mem : ∀ w ∈ s', ∃ z ∈ s, w = z / t := fun w hw => by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hw; exact ⟨z, hz, rfl⟩
  have hs'1 : ∀ w ∈ s', v w ≤ 1 := fun w hw => by
    obtain ⟨z, hz, rfl⟩ := hs'mem w hw
    rw [map_div₀, div_le_one₀ hvt]; exact htmax z hz

  have hPne : ∀ i ∈ s', (∏ j ∈ s'.erase i, (i - j)) ≠ 0 := fun i _ =>
    Finset.prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 (Finset.ne_of_mem_erase hj).symm
  have hPle : ∀ i ∈ s', v (∏ j ∈ s'.erase i, (i - j)) ≤ 1 := fun i hi => by
    rw [map_prod]
    refine Finset.prod_le_one (fun _ _ => zero_le') fun j hj => ?_
    exact (Valuation.map_sub _ _ _).trans (max_le (hs'1 i hi) (hs'1 j (Finset.mem_of_mem_erase hj)))
  set eStar : K := eM * t ^ ν * ∏ i ∈ s', ∏ j ∈ s'.erase i, (i - j) with heStar
  have heStar0 : eStar ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero heM0 (pow_ne_zero _ ht0)) ?_
    exact Finset.prod_ne_zero_iff.2 fun i hi => hPne i hi
  have hveStar_le : ∀ i ∈ s', v eStar ≤ M₀ * v t ^ ν * v (∏ j ∈ s'.erase i, (i - j)) := by
    intro i hi
    rw [heStar, map_mul, map_mul, map_pow, hveM, map_prod]
    apply mul_le_mul_right
    rw [← Finset.mul_prod_erase _ _ hi]
    refine mul_le_of_le_one_right' ?_
    exact Finset.prod_le_one (fun _ _ => zero_le') fun j hj => hPle j (Finset.mem_of_mem_erase hj)
  obtain ⟨N₂, hN₂⟩ := hung eStar heStar0
  set k := max k₀ N₂ with hkdef
  have hkk₀ : k₀ ≤ k := le_max_left _ _
  have hkN₀ : N₀ ≤ k := hk₀N₀.trans hkk₀

  set P' : K[X] := (r k).num.comp (C t * X) with hP'
  set Q' : K[X] := (r k).den.comp (C t * X) with hQ'
  have hQ'0 : Q'.coeff 0 = (r k).den.coeff 0 := by rw [hQ', comp_C_mul_X_coeff, pow_zero, mul_one]
  have hQ'0ne : Q'.coeff 0 ≠ 0 := by rw [hQ'0]; exact hcoef0 k
  have hQ'ne : Q' ≠ 0 := fun h => hQ'0ne (by rw [h, coeff_zero])
  have hQ'eval : ∀ w, Q'.eval w = (r k).den.eval (t * w) := fun w => by
    rw [hQ', eval_comp, eval_mul, eval_C, eval_X]
  have hP'eval : ∀ w, P'.eval w = (r k).num.eval (t * w) := fun w => by
    rw [hP', eval_comp, eval_mul, eval_C, eval_X]
  have hQ'roots : ∀ α ∈ Q'.roots, 1 < v α := fun α hα => by
    have hr : (r k).den.eval (t * α) = 0 := by rw [← hQ'eval]; exact (mem_roots hQ'ne).1 hα
    by_contra hle
    push Not at hle
    refine hpf k (t * α) (hS' _ ?_) hr
    rw [map_mul]
    calc v t * v α ≤ v t * 1 := mul_le_mul_right hle _
      _ < 1 := by rw [mul_one]; exact ht1
  have hQ'dom : ∀ i, 0 < i → v (Q'.coeff i) < v (Q'.coeff 0) := coeff_lt_coeff_zero_of_roots Q' hQ'ne hQ'roots
  have hT' : ∀ m, PowerSeries.coeff m (T P' Q') = c k m * t ^ m := fun m => by
    rw [hP', hQ']; exact T_comp_C_mul_X _ _ t (hcoef0 k) m
  have hvT' : ∀ m, v (PowerSeries.coeff m (T P' Q')) = v (c k m) * v t ^ m := fun m => by
    rw [hT', map_mul, map_pow]

  set d : ℕ → Γ₀ := fun m => v (c k m) * v t ^ m with hd
  have hdν : d ν = M₀ * v t ^ ν := by simp only [hd]; rw [hν k hkk₀]
  have hdbig : ∀ i, ν < i → d i < d ν := by
    intro i hi
    rw [hdν]
    calc d i = v (c k i) * v t ^ i := rfl
      _ ≤ M₀ * v t ^ i := mul_le_mul_left (hcoefM k hkN₀ i) _
      _ < M₀ * v t ^ ν := mul_lt_mul_of_pos_left (pow_lt_pow_right_of_lt_one₀ hvt ht1 hi) hM₀pos
  set R : Finset ℕ := Finset.range (ν + 1) with hR
  have hRne : R.Nonempty := ⟨0, by simp [hR]⟩
  obtain ⟨m₀, hm₀R, hm₀max⟩ := Finset.exists_max_image R d hRne
  set A : Finset ℕ := R.filter (fun m => ∀ i ∈ R, d i ≤ d m) with hAdef
  have hAne : A.Nonempty := ⟨m₀, Finset.mem_filter.2 ⟨hm₀R, hm₀max⟩⟩
  set n : ℕ := A.max' hAne with hndef
  have hnA : n ∈ A := Finset.max'_mem A hAne
  have hnR : n ∈ R := (Finset.mem_filter.1 hnA).1
  have hnν : n ≤ ν := by have := Finset.mem_range.1 hnR; omega
  have hnmax : ∀ i ∈ R, d i ≤ d n := (Finset.mem_filter.1 hnA).2
  have hle_n : ∀ i, d i ≤ d n := by
    intro i
    by_cases hi : i ≤ ν
    · exact hnmax i (Finset.mem_range.2 (by omega))
    · push Not at hi
      exact (hdbig i hi).le.trans (hnmax ν (Finset.mem_range.2 (by omega)))
  have hlt_n : ∀ j, n < j → d j < d n := by
    intro j hj
    by_cases hjν : j ≤ ν
    · have hjR : j ∈ R := Finset.mem_range.2 (by omega)
      have hjA : j ∉ A := fun hjA => absurd (Finset.le_max' A j hjA) (by rw [← hndef]; omega)
      rw [hAdef, Finset.mem_filter, not_and_or] at hjA
      rcases hjA with h | h
      · exact absurd hjR h
      · push Not at h
        obtain ⟨i, hiR, hlt⟩ := h
        exact hlt.trans_le (hnmax i hiR)
    · push Not at hjν
      exact (hdbig j hjν).trans_le (hnmax ν (Finset.mem_range.2 (by omega)))
  have hdn_pos : 0 < d n := by
    refine lt_of_lt_of_le ?_ (hle_n ν)
    rw [hdν]; exact mul_pos hM₀pos (pow_pos hvt _)

  obtain ⟨hPn, hPgt⟩ := coeff_dominant_of_T P' Q' hQ'0ne hQ'dom n
    (by rw [hvT']; exact hdn_pos) (fun i => by rw [hvT', hvT']; exact hle_n i)
    (fun j hj => by rw [hvT', hvT']; exact hlt_n j hj)
  rw [hvT'] at hPn hPgt
  set Mx : Γ₀ := d n * v (Q'.coeff 0) with hMx
  have hq0'pos : 0 < v (Q'.coeff 0) := (Valuation.pos_iff _).2 hQ'0ne
  have hMx0 : Mx ≠ 0 := (mul_pos hdn_pos hq0'pos).ne'

  set E : K[X] := Lagrange.interpolate s' id (fun w => P'.eval w) with hEdef
  have hvals : ∀ i ∈ s', v (P'.eval i) < Mx * v (∏ j ∈ s'.erase i, (i - j)) := by
    intro i hi
    obtain ⟨z, hz, rfl⟩ := hs'mem i hi
    obtain ⟨hz1, hzS, hfz⟩ := hsprop z hz
    have htz : t * (z / t) = z := by field_simp
    rw [hP'eval, htz]
    have hden : v ((r k).den.eval z) = v ((r k).den.coeff 0) := by
      rw [← hgQ k]
      refine v_eval_eq_gauss _ hz1.le fun α hα hα1 => ?_
      have hα1' : v α = 1 := le_antisymm hα1 (hroots k α hα)
      rw [Valuation.map_sub_eq_of_lt_right _ (by rw [hα1']; exact hz1), hα1']
    have hnum : (r k).num.eval z = (r k).evalAt z * (r k).den.eval z := by
      rw [RatPair.evalAt, div_mul_cancel₀ _ (hpf k z hzS)]
    have hsmall : v ((r k).evalAt z) < v eStar := by
      have h1 := hN₂ k (le_max_right _ _) ⟨z, hzS⟩
      rwa [hfz, sub_zero] at h1
    rw [hnum, map_mul, hden, ← hQ'0, hMx, mul_assoc, mul_comm (v (Q'.coeff 0)), ← mul_assoc]
    refine mul_lt_mul_of_pos_right ?_ hq0'pos
    calc v ((r k).evalAt z) < v eStar := hsmall
      _ ≤ M₀ * v t ^ ν * v (∏ j ∈ s'.erase (z / t), (z / t - j)) := hveStar_le _ hi
      _ = d ν * v (∏ j ∈ s'.erase (z / t), (z / t - j)) := by rw [hdν]
      _ ≤ d n * v (∏ j ∈ s'.erase (z / t), (z / t - j)) := mul_le_mul_left (hle_n ν) _
  have hE : ∀ m, v (E.coeff m) < Mx := fun m => v_coeff_interpolate_lt s' hs'1 _ hMx0 hvals m
  obtain ⟨hPEne, hcard⟩ := card_rin_sub_le P' E n hPn hPgt hE

  have hsub : s' ⊆ (rin (P' - E)).toFinset := by
    intro i hi
    rw [Multiset.mem_toFinset, rin, Multiset.mem_filter]
    refine ⟨(mem_roots hPEne).2 ?_, hs'1 i hi⟩
    have hnode := Lagrange.eval_interpolate_at_node (fun w => P'.eval w) (Set.injOn_id (s' : Set K)) hi
    simp only [id] at hnode
    rw [IsRoot, eval_sub, sub_eq_zero, hEdef, hnode]
  have := (Finset.card_le_card hsub).trans (Multiset.toFinset_card_le _)
  rw [hs'card] at this
  omega

end ZC0

end IdDisc

namespace IdDisc

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

section NewtonPolygon2

variable [IsAlgClosed K]

open scoped Classical

theorem v_coeff_lt_gauss_of_card_rin_lt (B : K[X]) (hB : B ≠ 0) {j : ℕ} (hj : (rin B).card < j) :
    v (B.coeff j) < gauss B := by
  set m := (rin B).card with hm
  have hdeg : (Bin B).natDegree = m := natDegree_Bin B
  have hfac := eq_C_mul_Bin_mul_Bout B
  have hlc : v B.leadingCoeff ≠ 0 := (Valuation.ne_zero_iff _).2 (leadingCoeff_ne_zero.2 hB)
  have key : v ((Bin B * Bout B).coeff j) < gauss (Bin B) * gauss (Bout B) := by
    rw [coeff_mul]
    apply Valuation.map_sum_lt
    · rw [gauss_Bin, one_mul, gauss_Bout]; exact (Valuation.ne_zero_iff _).2 (Bout_coeff_zero_ne B)
    · intro x hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      rw [map_mul, gauss_Bin, one_mul, gauss_Bout]
      by_cases h1 : x.1 ≤ m
      · have hx2 : 0 < x.2 := by omega
        calc v ((Bin B).coeff x.1) * v ((Bout B).coeff x.2) ≤ 1 * v ((Bout B).coeff x.2) :=
              mul_le_mul_left ((v_coeff_le_gauss _ _).trans (gauss_Bin B).le) _
          _ < v ((Bout B).coeff 0) := by rw [one_mul]; exact coeff_Bout_lt B hx2
      · push Not at h1
        rw [coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact h1), map_zero, zero_mul]
        exact (Valuation.pos_iff _).2 (Bout_coeff_zero_ne B)
  have hcoeff : B.coeff j = B.leadingCoeff * (Bin B * Bout B).coeff j := by
    conv_lhs => rw [hfac]
    rw [coeff_C_mul]
  have hg : gauss B = v B.leadingCoeff * (gauss (Bin B) * gauss (Bout B)) := by
    conv_lhs => rw [hfac]
    rw [gauss_C_mul, gauss_mul]
  rw [hcoeff, map_mul, hg]
  exact mul_lt_mul_of_pos_left key (zero_lt_iff.2 hlc)

theorem exists_root_of_gauss_le (B : K[X]) (hB : B ≠ 0) {j : ℕ} (hj : 0 < j) (hle : gauss B ≤ v (B.coeff j)) :
    ∃ β : K, B.eval β = 0 ∧ v β ≤ 1 := by
  have hm : 0 < (rin B).card := by
    by_contra h0
    push Not at h0
    have : (rin B).card < j := by omega
    exact absurd (v_coeff_lt_gauss_of_card_rin_lt B hB this) (not_lt.2 hle)
  obtain ⟨β, hβ⟩ := Multiset.card_pos_iff_exists_mem.1 hm
  rw [rin, Multiset.mem_filter] at hβ
  exact ⟨β, (mem_roots hB).1 hβ.1, hβ.2⟩

theorem v_eval_eq_gauss_mul_prod (B : K[X]) {α : K} (hα : v α ≤ 1) :
    v (B.eval α) = gauss B * ((rin B).map fun β => v (α - β)).prod := by
  conv_lhs => rw [eq_C_mul_prod B]
  rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, map_mul, map_multiset_prod, Multiset.map_map,
    gauss_eq_prod_roots, mul_assoc]
  congr 1
  have hsplit : B.roots = rin B + rout B := (Multiset.filter_add_not _ _).symm
  conv_lhs => rw [hsplit]
  conv_rhs => rw [hsplit]
  rw [Multiset.map_add, Multiset.prod_add, Multiset.map_add, Multiset.prod_add]
  have hin : ((rin B).map fun β => max 1 (v β)).prod = 1 := by
    rw [Multiset.prod_eq_one]
    intro x hx
    obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.1 hx
    exact max_eq_left (Multiset.mem_filter.1 hβ).2
  have hout : ((rout B).map (fun β => v ((X - C β).eval α)) ).prod = ((rout B).map fun β => max 1 (v β)).prod := by
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun β hβ => ?_)
    have hb : 1 < v β := not_le.1 (Multiset.mem_filter.1 hβ).2
    simp only [eval_sub, eval_X, eval_C]
    rw [max_eq_right hb.le]
    exact Valuation.map_sub_eq_of_lt_right _ (hα.trans_lt hb)
  have hin' : ((rin B).map (fun β => v ((X - C β).eval α))).prod = ((rin B).map fun β => v (α - β)).prod := by
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun β _ => ?_)
    simp only [eval_sub, eval_X, eval_C]
  simp only [Function.comp_def]
  rw [hin', hout, hin, one_mul, mul_comm]

theorem exists_rin_v_sub_le (B : K[X]) {α : K} (hα : v α ≤ 1) {σ : Γ₀} (hN : 0 < (rin B).card)
    (hB : B ≠ 0) (hval : v (B.eval α) ≤ gauss B * σ ^ (rin B).card) : ∃ β ∈ rin B, v (α - β) ≤ σ := by
  by_contra hno
  push Not at hno
  have hprod : σ ^ (rin B).card < ((rin B).map fun β => v (α - β)).prod := by

    have key : ∀ s : Multiset K, (∀ β ∈ s, σ < v (α - β)) → 0 < s.card →
        σ ^ s.card < (s.map fun β => v (α - β)).prod := by
      intro s
      induction s using Multiset.induction_on with
      | empty => intro _ h; simp at h
      | cons b s ih =>
        intro hs _
        rw [Multiset.card_cons, pow_succ, Multiset.map_cons, Multiset.prod_cons]
        have hb := hs b (Multiset.mem_cons_self _ _)
        by_cases hs0 : s.card = 0
        · rw [Multiset.card_eq_zero.1 hs0]; simpa using hb
        · have := ih (fun β hβ => hs β (Multiset.mem_cons_of_mem hβ)) (Nat.pos_of_ne_zero hs0)
          rw [mul_comm (σ ^ s.card) σ]
          exact mul_lt_mul'' hb this zero_le' zero_le'
    exact key _ hno hN
  have := v_eval_eq_gauss_mul_prod B hα
  have hlt : gauss B * σ ^ (rin B).card < v (B.eval α) := by
    rw [this]; exact mul_lt_mul_of_pos_left hprod (gauss_pos hB)
  exact absurd hval (not_le.2 hlt)

end NewtonPolygon2

end IdDisc

namespace IdDisc

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

section RootsBelow

variable [IsAlgClosed K]

open scoped Classical

theorem eval_comp_C_mul_X' (P : K[X]) (z w : K) : (P.comp (C z * X)).eval w = P.eval (z * w) := by
  rw [eval_comp, eval_mul, eval_C, eval_X]

theorem comp_C_mul_X_ne_zero {P : K[X]} (hP : P ≠ 0) {z : K} (hz : z ≠ 0) : P.comp (C z * X) ≠ 0 := by
  rw [Ne, comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_of_ne_zero hz)]; exact hP

theorem one_lt_of_mem_roots_comp (Q : K[X]) (hQ : Q ≠ 0) (hQroots : ∀ α ∈ Q.roots, 1 ≤ v α)
    {z : K} (hz0 : z ≠ 0) (hz1 : v z < 1) : ∀ α ∈ (Q.comp (C z * X)).roots, 1 < v α := by
  intro α hα
  have hr : Q.eval (z * α) = 0 := by
    rw [← eval_comp_C_mul_X']; exact (mem_roots (comp_C_mul_X_ne_zero hQ hz0)).1 hα
  have h1 := hQroots (z * α) ((mem_roots hQ).2 hr)
  rw [map_mul] at h1
  by_contra hle
  push Not at hle
  have : v z * v α < 1 := by
    calc v z * v α ≤ v z * 1 := mul_le_mul_right hle _
      _ < 1 := by rw [mul_one]; exact hz1
  exact absurd h1 (not_le.2 this)

theorem exists_root_of_v_eval_div_lt (P Q : K[X]) (hP : P ≠ 0) (hQroots : ∀ α ∈ Q.roots, 1 ≤ v α)
    {z : K} (hz0 : z ≠ 0) (hz1 : v z < 1)
    (hlt : v (P.eval z / Q.eval z) < v (P.eval 0 / Q.eval 0)) :
    ∃ β : K, P.eval β = 0 ∧ v β ≤ v z := by
  set B : K[X] := P.comp (C z * X) with hB
  have hBne : B ≠ 0 := comp_C_mul_X_ne_zero hP hz0
  by_cases hQ : Q = 0
  · exfalso; rw [hQ, eval_zero, eval_zero, div_zero, div_zero] at hlt; exact lt_irrefl _ hlt

  have hQz : v (Q.eval z) = v (Q.eval 0) := by
    rw [← coeff_zero_eq_eval_zero, ← gauss_eq_coeff_zero_of_roots Q hQroots]
    refine v_eval_eq_gauss Q hz1.le fun α hα hα1 => ?_
    have : v α = 1 := le_antisymm hα1 (hQroots α hα)
    rw [Valuation.map_sub_eq_of_lt_right _ (by rw [this]; exact hz1), this]

  by_contra hno
  push Not at hno
  have hrin : ∀ β ∈ B.roots, 1 < v β := by
    intro β hβ
    by_contra hle
    push Not at hle
    have hr : P.eval (z * β) = 0 := by rw [← eval_comp_C_mul_X']; exact (mem_roots hBne).1 hβ
    have := hno (z * β) hr
    rw [map_mul] at this
    exact absurd (mul_le_of_le_one_right' hle) (not_le.2 this)
  have hB1 : v (B.eval 1) = v (B.coeff 0) := by
    rw [← gauss_eq_coeff_zero_of_roots B (fun β hβ => (hrin β hβ).le)]
    exact v_eval_eq_gauss B (le_of_eq (map_one _)) fun β hβ hβ1 => absurd hβ1 (not_le.2 (hrin β hβ))
  have hPz : v (P.eval z) = v (P.eval 0) := by
    have e1 : P.eval z = B.eval 1 := by rw [hB, eval_comp_C_mul_X', mul_one]
    have e2 : B.coeff 0 = P.eval 0 := by rw [hB, comp_C_mul_X_coeff, pow_zero, mul_one, coeff_zero_eq_eval_zero]
    rw [e1, hB1, e2]
  rw [map_div₀, map_div₀, hPz, hQz] at hlt
  exact lt_irrefl _ hlt

theorem exists_last_max (c : ℕ → Γ₀) {M : Γ₀} (hMpos : 0 < M) (hM : ∀ j, c j ≤ M) (ν : ℕ) (hν : c ν = M)
    {ρ : Γ₀} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ n : ℕ, n ≤ ν ∧ (∀ i, c i * ρ ^ i ≤ c n * ρ ^ n) ∧ (∀ j, n < j → c j * ρ ^ j < c n * ρ ^ n) ∧
      0 < c n * ρ ^ n := by
  set d : ℕ → Γ₀ := fun m => c m * ρ ^ m with hd
  have hdν : d ν = M * ρ ^ ν := by simp only [hd]; rw [hν]
  have hdbig : ∀ i, ν < i → d i < d ν := by
    intro i hi
    rw [hdν]
    calc d i = c i * ρ ^ i := rfl
      _ ≤ M * ρ ^ i := mul_le_mul_left (hM i) _
      _ < M * ρ ^ ν := mul_lt_mul_of_pos_left (pow_lt_pow_right_of_lt_one₀ hρ0 hρ1 hi) hMpos
  set R : Finset ℕ := Finset.range (ν + 1) with hR
  obtain ⟨m₀, hm₀R, hm₀max⟩ := Finset.exists_max_image R d ⟨0, by simp [hR]⟩
  set A : Finset ℕ := R.filter (fun m => ∀ i ∈ R, d i ≤ d m) with hAdef
  have hAne : A.Nonempty := ⟨m₀, Finset.mem_filter.2 ⟨hm₀R, hm₀max⟩⟩
  set n : ℕ := A.max' hAne with hndef
  have hnA : n ∈ A := Finset.max'_mem A hAne
  have hnR : n ∈ R := (Finset.mem_filter.1 hnA).1
  have hnν : n ≤ ν := by have := Finset.mem_range.1 hnR; omega
  have hnmax : ∀ i ∈ R, d i ≤ d n := (Finset.mem_filter.1 hnA).2
  have hle_n : ∀ i, d i ≤ d n := by
    intro i
    by_cases hi : i ≤ ν
    · exact hnmax i (Finset.mem_range.2 (by omega))
    · push Not at hi
      exact (hdbig i hi).le.trans (hnmax ν (Finset.mem_range.2 (by omega)))
  have hlt_n : ∀ j, n < j → d j < d n := by
    intro j hj
    by_cases hjν : j ≤ ν
    · have hjR : j ∈ R := Finset.mem_range.2 (by omega)
      have hjA : j ∉ A := fun hjA => absurd (Finset.le_max' A j hjA) (by rw [← hndef]; omega)
      rw [hAdef, Finset.mem_filter, not_and_or] at hjA
      rcases hjA with h | h
      · exact absurd hjR h
      · push Not at h
        obtain ⟨i, hiR, hlt⟩ := h
        exact hlt.trans_le (hnmax i hiR)
    · push Not at hjν
      exact (hdbig j hjν).trans_le (hnmax ν (Finset.mem_range.2 (by omega)))
  have hpos : 0 < d n := lt_of_lt_of_le (by rw [hdν]; exact mul_pos hMpos (pow_pos hρ0 _)) (hle_n ν)
  exact ⟨n, hnν, hle_n, hlt_n, hpos⟩

theorem card_rin_comp_le (P Q : K[X]) (hQ0 : Q.coeff 0 ≠ 0) (hQroots : ∀ α ∈ Q.roots, 1 ≤ v α)
    {z : K} (hz0 : z ≠ 0) (hz1 : v z < 1) {M : Γ₀} (hMpos : 0 < M)
    (hM : ∀ j, v (PowerSeries.coeff j (T P Q)) ≤ M) (ν : ℕ) (hν : v (PowerSeries.coeff ν (T P Q)) = M) :
    (rin (P.comp (C z * X))).card ≤ ν := by
  have hQne : Q ≠ 0 := fun h => hQ0 (by rw [h, coeff_zero])
  set P' : K[X] := P.comp (C z * X) with hP'
  set Q' : K[X] := Q.comp (C z * X) with hQ'
  have hQ'0 : Q'.coeff 0 = Q.coeff 0 := by rw [hQ', comp_C_mul_X_coeff, pow_zero, mul_one]
  have hQ'0ne : Q'.coeff 0 ≠ 0 := by rw [hQ'0]; exact hQ0
  have hQ'ne : Q' ≠ 0 := comp_C_mul_X_ne_zero hQne hz0
  have hQ'dom : ∀ i, 0 < i → v (Q'.coeff i) < v (Q'.coeff 0) :=
    coeff_lt_coeff_zero_of_roots Q' hQ'ne (one_lt_of_mem_roots_comp Q hQne hQroots hz0 hz1)
  have hvT' : ∀ m, v (PowerSeries.coeff m (T P' Q')) = v (PowerSeries.coeff m (T P Q)) * v z ^ m := fun m => by
    rw [hP', hQ', T_comp_C_mul_X _ _ z hQ0, map_mul, map_pow]
  have hvz : 0 < v z := (Valuation.pos_iff _).2 hz0
  obtain ⟨n, hnν, hle_n, hlt_n, hpos⟩ :=
    exists_last_max (fun j => v (PowerSeries.coeff j (T P Q))) hMpos hM ν hν hvz hz1
  by_cases hP : P = 0
  · have : P' = 0 := by rw [hP', hP, zero_comp]
    rw [this, rin, roots_zero]; simp
  have hP'ne : P' ≠ 0 := comp_C_mul_X_ne_zero hP hz0
  obtain ⟨hPn, hPgt⟩ := coeff_dominant_of_T P' Q' hQ'0ne hQ'dom n
    (by rw [hvT']; exact hpos) (fun i => by rw [hvT', hvT']; exact hle_n i)
    (fun j hj => by rw [hvT', hvT']; exact hlt_n j hj)
  refine (card_rin_le P' hP'ne n fun j hj => ?_).trans hnν
  rw [hPn]; exact hPgt j hj

theorem exists_root_v_sub_le (P Q : K[X]) (hQ0 : Q.coeff 0 ≠ 0) (hQroots : ∀ α ∈ Q.roots, 1 ≤ v α)
    {z : K} (hz0 : z ≠ 0) (hz1 : v z < 1) {M : Γ₀} (hMpos : 0 < M)
    (hM : ∀ j, v (PowerSeries.coeff j (T P Q)) ≤ M) (ν : ℕ) (hν : v (PowerSeries.coeff ν (T P Q)) = M)
    (hex : ∃ β : K, P.eval β = 0 ∧ v β ≤ v z)
    {α : K} (hα : v α ≤ v z) {σ : Γ₀} (hσ : σ ≤ 1)
    (hval : v (P.eval α) ≤ M * v (Q.coeff 0) * v z ^ ν * σ ^ ν) :
    ∃ β : K, P.eval β = 0 ∧ v β ≤ v z ∧ v (α - β) ≤ v z * σ := by
  have hvz : 0 < v z := (Valuation.pos_iff _).2 hz0
  obtain ⟨β₀, hβ₀, hβ₀z⟩ := hex
  by_cases hP : P = 0
  · refine ⟨α, by rw [hP, eval_zero], hα, by rw [sub_self, map_zero]; exact zero_le'⟩
  set B : K[X] := P.comp (C z * X) with hB
  have hBne : B ≠ 0 := comp_C_mul_X_ne_zero hP hz0
  set Q' : K[X] := Q.comp (C z * X) with hQ'
  have hQ'0 : Q'.coeff 0 = Q.coeff 0 := by rw [hQ', comp_C_mul_X_coeff, pow_zero, mul_one]
  have hQ'0ne : Q'.coeff 0 ≠ 0 := by rw [hQ'0]; exact hQ0
  have hQne : Q ≠ 0 := fun h => hQ0 (by rw [h, coeff_zero])
  have hQ'ne : Q' ≠ 0 := comp_C_mul_X_ne_zero hQne hz0
  have hQ'roots : ∀ γ ∈ Q'.roots, 1 ≤ v γ := fun γ hγ => (one_lt_of_mem_roots_comp Q hQne hQroots hz0 hz1 γ hγ).le
  have hgQ' : gauss Q' = v (Q'.coeff 0) := gauss_eq_coeff_zero_of_roots Q' hQ'roots
  have hQ'coef : ∀ i, v (Q'.coeff i) ≤ v (Q'.coeff 0) := fun i => hgQ' ▸ v_coeff_le_gauss Q' i

  have hTν : v (PowerSeries.coeff ν (T B Q')) = M * v z ^ ν := by
    rw [hB, hQ', T_comp_C_mul_X _ _ z hQ0, map_mul, map_pow, hν]
  have hgB : M * v z ^ ν * v (Q.coeff 0) ≤ gauss B := by
    have h1 := v_coeff_T_le B Q' hQ'0ne hQ'coef ν
    rw [hTν, hQ'0] at h1
    have hq0 : 0 < v (Q.coeff 0) := (Valuation.pos_iff _).2 hQ0
    rwa [le_mul_inv_iff₀ hq0] at h1

  set N := (rin B).card with hN
  have hNν : N ≤ ν := card_rin_comp_le P Q hQ0 hQroots hz0 hz1 hMpos hM ν hν
  have hNpos : 0 < N := by
    refine Multiset.card_pos_iff_exists_mem.2 ⟨β₀ / z, ?_⟩
    rw [rin, Multiset.mem_filter]
    refine ⟨(mem_roots hBne).2 ?_, ?_⟩
    · rw [IsRoot, hB, eval_comp_C_mul_X', mul_div_cancel₀ _ hz0]; exact hβ₀
    · rw [map_div₀, div_le_one₀ hvz]; exact hβ₀z

  have hα' : v (α / z) ≤ 1 := by rw [map_div₀, div_le_one₀ hvz]; exact hα
  have hvalB : v (B.eval (α / z)) ≤ gauss B * σ ^ N := by
    rw [hB, eval_comp_C_mul_X', mul_div_cancel₀ _ hz0]
    calc v (P.eval α) ≤ M * v (Q.coeff 0) * v z ^ ν * σ ^ ν := hval
      _ = (M * v z ^ ν * v (Q.coeff 0)) * σ ^ ν := by rw [mul_right_comm M (v (Q.coeff 0)) (v z ^ ν)]
      _ ≤ gauss B * σ ^ ν := mul_le_mul_left hgB _
      _ ≤ gauss B * σ ^ N := mul_le_mul_right (pow_le_pow_right_of_le_one' hσ hNν) _
  obtain ⟨β', hβ', hclose⟩ := exists_rin_v_sub_le B hα' hNpos hBne hvalB
  rw [rin, Multiset.mem_filter] at hβ'
  refine ⟨z * β', ?_, ?_, ?_⟩
  · rw [← eval_comp_C_mul_X', ← hB]; exact (mem_roots hBne).1 hβ'.1
  · rw [map_mul]; exact mul_le_of_le_one_right' hβ'.2
  · have : α - z * β' = z * (α / z - β') := by field_simp
    rw [this, map_mul]
    exact mul_le_mul_right hclose _

end RootsBelow

end IdDisc

namespace MMCplumb

open Polynomial Filter

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))
local notation "VG" => MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass (Valued.v (R := K) (Γ₀ := Γ₀)))

theorem exists_restrict_eq (γ : VGˣ) : ∃ y : K, y ≠ 0 ∧ (Valued.v (R := K) (Γ₀ := Γ₀)).restrict y = γ.val := by
  obtain ⟨y, hy⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
    (f := (MonoidWithZeroHom.ofClass (Valued.v (R := K) (Γ₀ := Γ₀)))) γ.val
  refine ⟨y, fun h0 => ?_, ?_⟩
  · apply γ.ne_zero
    rw [← hy, h0, map_zero]
  · rw [Valuation.restrict_def]; exact hy

theorem v_sub_le_of_succ {a : ℕ → K} {γ : ℕ → Γ₀} (hγ : Antitone γ)
    (h : ∀ i, v (a (i + 1) - a i) ≤ γ i) : ∀ i j, i ≤ j → v (a j - a i) ≤ γ i := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => rw [sub_self, map_zero]; exact zero_le'
  | succ j hij ih =>
    have e : a (j + 1) - a i = (a (j + 1) - a j) + (a j - a i) := by ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans (max_le ((h j).trans (hγ hij)) ih)

theorem exists_forall_pow_lt (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    {z : K} (hz0 : z ≠ 0) (hz1 : v z < 1) {e : K} (he : e ≠ 0) : ∃ n : ℕ, ∀ m ≥ n, v z ^ m < v e := by
  obtain ⟨n, hn⟩ := hrk z (e * z) hz1 (mul_ne_zero he hz0)
  refine ⟨n, fun m hm => ?_⟩
  have hve : 0 < v e := (Valuation.pos_iff _).mpr he
  calc v z ^ m ≤ v z ^ n := pow_le_pow_right_of_le_one' hz1.le hm
    _ ≤ v (e * z) := hn
    _ = v e * v z := map_mul _ _ _
    _ < v e * 1 := mul_lt_mul_of_pos_left hz1 hve
    _ = v e := mul_one _

theorem cauchySeq_of_v_sub_succ_le
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (a : ℕ → K) (C z : K) (hz1 : v z < 1)
    (h : ∀ i, v (a (i + 1) - a i) ≤ v C * v z ^ i) : CauchySeq a := by
  have hanti : Antitone fun i : ℕ => v C * v z ^ i :=
    fun i j hij => mul_le_mul' le_rfl (pow_le_pow_right_of_le_one' hz1.le hij)
  have htel := v_sub_le_of_succ hanti h
  rw [(Valued.hasBasis_uniformity K Γ₀).cauchySeq_iff]
  intro γ _
  obtain ⟨y, hy0, hy⟩ := exists_restrict_eq (K := K) γ

  have hN : ∃ N : ℕ, v C * v z ^ N < v y := by
    have hvy : 0 < v y := (Valuation.pos_iff _).mpr hy0
    by_cases hC : C = 0
    · exact ⟨0, by rw [hC, map_zero, zero_mul]; exact hvy⟩
    by_cases hz : z = 0
    · exact ⟨1, by rw [hz, map_zero, pow_one, mul_zero]; exact hvy⟩
    have hvC : 0 < v C := (Valuation.pos_iff _).mpr hC
    obtain ⟨n, hn⟩ := exists_forall_pow_lt hrk hz hz1 (e := y / C) (div_ne_zero hy0 hC)
    refine ⟨n, ?_⟩
    have := hn n le_rfl
    rw [map_div₀, lt_div_iff₀ hvC] at this
    rwa [mul_comm]
  obtain ⟨N, hN⟩ := hN
  refine ⟨N, fun m hm n hn => ?_⟩
  show Valued.v.restrict (a n - a m) < γ.val
  rw [← hy, Valued.v.restrict_lt_iff]
  rcases le_total m n with hmn | hnm
  · exact ((htel m n hmn).trans (hanti hm)).trans_lt hN
  · rw [Valuation.map_sub_swap]
    exact ((htel n m hnm).trans (hanti hn)).trans_lt hN

theorem exists_forall_v_sub_lt_of_tendsto (a : ℕ → K) (x : K) (h : Tendsto a atTop (nhds x))
    (e : K) (he : e ≠ 0) : ∃ N : ℕ, ∀ i ≥ N, v (a i - x) < v e := by
  have hre : Valued.v.restrict e ≠ (0 : VG) := fun h0 =>
    he ((Valuation.zero_iff _).mp ((Valued.v.restrict_eq_zero_iff).mp h0))
  have hU : {y : K | v (y - x) < v e} ∈ nhds x := by
    rw [Valued.mem_nhds]
    refine ⟨Units.mk0 _ hre, fun y hy => ?_⟩
    have hy' : Valued.v.restrict (y - x) < Valued.v.restrict e := by simpa only [Set.mem_setOf_eq, Units.val_mk0] using hy
    exact (Valued.v.restrict_lt_iff).1 hy'
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h hU)
  exact ⟨N, fun i hi => hN i hi⟩

theorem exists_tendsto_of_cauchySeq_of_v_sub_le [CompleteSpace K] (a : ℕ → K) (ha : CauchySeq a)
    (c : K) (ρ : Γ₀) (hρ : ∀ i, v (a i - c) ≤ ρ) :
    ∃ x : K, Tendsto a atTop (nhds x) ∧ v (x - c) ≤ ρ := by
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete ha
  refine ⟨x, hx, ?_⟩
  by_contra hgt
  rw [not_le] at hgt
  have hxc : x - c ≠ 0 := (Valuation.pos_iff _).mp (lt_of_le_of_lt zero_le' hgt)
  obtain ⟨N, hN⟩ := exists_forall_v_sub_lt_of_tendsto a x hx (x - c) hxc
  have h1 := hN N le_rfl
  have e : a N - c = (a N - x) + (x - c) := by ring
  have : v (a N - c) = v (x - c) := by rw [e]; exact Valuation.map_add_eq_of_lt_right _ h1
  exact absurd (hρ N) (by rw [this, not_le]; exact hgt)

theorem forall_eventually_v_sub_lt {α : Type} {F : ℕ → α → K} {φ : α → K} (h : TendstoUniformly F φ atTop)
    (e : K) (he : e ≠ 0) : ∃ N : ℕ, ∀ k ≥ N, ∀ t : α, v (F k t - φ t) < v e := by
  have hre : Valued.v.restrict e ≠ (0 : VG) := fun h0 =>
    he ((Valuation.zero_iff _).mp ((Valued.v.restrict_eq_zero_iff).mp h0))
  have hU := h _ ((Valued.hasBasis_uniformity K Γ₀).mem_of_mem (i := Units.mk0 _ hre) trivial)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hU
  refine ⟨N, fun k hk t => ?_⟩
  have h1 : Valued.v.restrict (F k t - φ t) < Valued.v.restrict e := by simpa only [Set.mem_setOf_eq, Units.val_mk0] using hN k hk t
  exact (Valued.v.restrict_lt_iff).1 h1

theorem eq_of_forall_v_sub_lt (hnco : ∃ γ : Γ₀ˣ, ∀ y : K, y ≠ 0 → (γ : Γ₀) ≤ v y) {x y : K}
    (h : ∀ γ : Γ₀ˣ, v (x - y) < γ) : x = y := by
  obtain ⟨γ, hγ⟩ := hnco
  by_contra hne
  exact absurd (hγ (x - y) (sub_ne_zero.mpr hne)) (not_le.mpr (h γ))

end MMCplumb

namespace IdDisc

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

section ZM0

variable [IsAlgClosed K]

open scoped Classical

theorem zm0 [CompleteSpace K]
    (hrk : ∀ x y : K, v x < 1 → y ≠ 0 → ∃ n : ℕ, v x ^ n ≤ v y)
    (S : Set K) (Z : Finset K) (hZ : ∀ ζ ∈ Z, v ζ = 1)
    (hS : ∀ y : K, v y ≤ 1 → (∀ ζ ∈ Z, 1 ≤ v (y - ζ)) → y ∈ S)
    {f : ↥S → K} (hf : f ∈ holOn K S) (h0 : ∀ y : ↥S, v (y : K) < 1 → f y ≠ 0) :
    ∃ δ : K, δ ≠ 0 ∧ ∀ y : ↥S, v (y : K) < 1 → v δ ≤ v (f y) := by
  obtain ⟨r, hpf, -, hlim⟩ := hf
  have hung := unif_eps hlim

  have hS' : ∀ y : K, v y < 1 → y ∈ S := fun y hy => hS y hy.le fun ζ hζ => by
    rw [Valuation.map_sub_eq_of_lt_right _ (by rw [hZ ζ hζ]; exact hy), hZ ζ hζ]
  have hden0 : ∀ k, (r k).den.eval 0 ≠ 0 := fun k => hpf k 0 (hS' 0 (by rw [map_zero]; exact zero_lt_one))
  have hcoef0 : ∀ k, (r k).den.coeff 0 ≠ 0 := fun k => by rw [coeff_zero_eq_eval_zero]; exact hden0 k
  have hden_ne : ∀ k, (r k).den ≠ 0 := fun k h => hcoef0 k (by rw [h, coeff_zero])
  have hroots : ∀ k, ∀ α ∈ (r k).den.roots, 1 ≤ v α := fun k α hα => by
    by_contra hlt
    push Not at hlt
    exact hpf k α (hS' α hlt) ((mem_roots (hden_ne k)).1 hα)
  have hrootsZ : ∀ k (y : K), v y ≤ 1 → (∀ ζ ∈ Z, 1 ≤ v (y - ζ)) →
      ∀ α ∈ (r k).den.roots, v α ≤ 1 → 1 ≤ v (y - α) := by
    intro k y _ hyZ α hα hα1
    by_contra hlt
    push Not at hlt
    refine hpf k α (hS α hα1 fun ζ hζ => ?_) ((mem_roots (hden_ne k)).1 hα)
    have : α - ζ = (y - ζ) - (y - α) := by ring
    rw [this, Valuation.map_sub_eq_of_lt_left _ (hlt.trans_le (hyZ ζ hζ))]
    exact hyZ ζ hζ
  have hgQ : ∀ k, gauss (r k).den = v ((r k).den.coeff 0) := fun k =>
    gauss_eq_coeff_zero_of_roots _ (hroots k)
  have hQcoef : ∀ k i, v ((r k).den.coeff i) ≤ v ((r k).den.coeff 0) := fun k i =>
    (hgQ k) ▸ v_coeff_le_gauss _ i
  have hgQpos : ∀ k, 0 < gauss (r k).den := fun k => gauss_pos (hden_ne k)

  have hC : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ y ∈ S,
      v ((r k).evalAt y - (r j).evalAt y) < v e := fun e he => by
    obtain ⟨N, hN⟩ := hung e he
    refine ⟨N, fun k hk j hj y hy => ?_⟩
    have : (r k).evalAt y - (r j).evalAt y = ((r k).evalAt y - f ⟨y, hy⟩) - ((r j).evalAt y - f ⟨y, hy⟩) := by
      ring
    rw [this]
    exact Valuation.map_sub_lt _ (hN k hk ⟨y, hy⟩) (hN j hj ⟨y, hy⟩)

  have hvalF : ∀ k (y : K), v y ≤ 1 → (∀ ζ ∈ Z, 1 ≤ v (y - ζ)) →
      v ((r k).evalAt y) ≤ gauss (r k).num / gauss (r k).den := by
    intro k y hy1 hyZ
    have hQy : v ((r k).den.eval y) = gauss (r k).den := v_eval_eq_gauss _ hy1 (hrootsZ k y hy1 hyZ)
    show v ((r k).num.eval y / (r k).den.eval y) ≤ _
    rw [map_div₀, hQy]
    exact div_le_div_of_nonneg_right (v_eval_le_gauss _ hy1) (hgQpos k).le

  have hvalgen : ∀ k (y : K), v y ≤ 1 → (∀ b ∈ (r k).num.roots + (r k).den.roots, v b ≤ 1 → 1 ≤ v (y - b)) →
      v ((r k).evalAt y) = gauss (r k).num / gauss (r k).den := by
    intro k y hy1 hgen
    show v ((r k).num.eval y / (r k).den.eval y) = _
    rw [map_div₀, v_eval_eq_gauss _ hy1 (fun α hα => hgen α (Multiset.mem_add.2 (Or.inl hα))),
      v_eval_eq_gauss _ hy1 (fun α hα => hgen α (Multiset.mem_add.2 (Or.inr hα)))]
  have h0S : (0 : K) ∈ S := hS' 0 (by rw [map_zero]; exact zero_lt_one)
  have hf0 : f ⟨0, h0S⟩ ≠ 0 := h0 ⟨0, h0S⟩ (by show v (0 : K) < 1; rw [map_zero]; exact zero_lt_one)

  by_cases hI : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, gauss (r k).num / gauss (r k).den < v e
  · exfalso
    apply hf0
    by_contra hfy
    obtain ⟨N₁, hN₁⟩ := hI (f ⟨0, h0S⟩) hfy
    obtain ⟨N₂, hN₂⟩ := hung (f ⟨0, h0S⟩) hfy
    set k := max N₁ N₂
    have h1 : v ((r k).evalAt 0) < v (f ⟨0, h0S⟩) :=
      (hvalF k 0 (by rw [map_zero]; exact zero_le') (fun ζ hζ => by rw [zero_sub, Valuation.map_neg, hZ ζ hζ])).trans_lt
        (hN₁ k (le_max_left _ _))
    have h2 : v ((r k).evalAt 0 - f ⟨0, h0S⟩) < v (f ⟨0, h0S⟩) := hN₂ k (le_max_right _ _) ⟨0, h0S⟩
    have : f ⟨0, h0S⟩ = (r k).evalAt 0 - ((r k).evalAt 0 - f ⟨0, h0S⟩) := by ring
    have h3 : v (f ⟨0, h0S⟩) < v (f ⟨0, h0S⟩) := by
      conv_lhs => rw [this]
      exact Valuation.map_sub_lt _ h1 h2
    exact lt_irrefl _ h3

  push Not at hI
  obtain ⟨e₀, he₀, hfreq⟩ := hI

  obtain ⟨N₀, hN₀⟩ := hC e₀ he₀

  let c : ℕ → ℕ → K := fun k m => PowerSeries.coeff m (T (r k).num (r k).den)
  have hZ' : ∀ ζ ∈ Z, 1 ≤ v ζ := fun ζ hζ => (hZ ζ hζ).ge
  have hA : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ m, v (c k m - c j m) < v e := by
    intro e he
    obtain ⟨N, hN⟩ := hC e he
    refine ⟨N, fun k hk j hj m => ?_⟩
    set P := (r k).num * (r j).den - (r j).num * (r k).den with hP
    set Q := (r k).den * (r j).den with hQ
    have hQ0 : Q.coeff 0 ≠ 0 := by rw [hQ, mul_coeff_zero]; exact mul_ne_zero (hcoef0 k) (hcoef0 j)
    have hQne : Q ≠ 0 := mul_ne_zero (hden_ne k) (hden_ne j)
    have hbT : c k m - c j m = PowerSeries.coeff m (T P Q) := by
      simp only [c]; rw [hP, hQ, T_sub _ _ _ _ (hcoef0 k) (hcoef0 j), map_sub]
    rw [hbT]
    have hQroots : ∀ α ∈ Q.roots, 1 ≤ v α := fun α hα => by
      rw [hQ, roots_mul hQne, Multiset.mem_add] at hα
      rcases hα with hα | hα
      · exact hroots k α hα
      · exact hroots j α hα
    have hgQ' : gauss Q = v (Q.coeff 0) := gauss_eq_coeff_zero_of_roots Q hQroots
    have hQcoef' : ∀ i, v (Q.coeff i) ≤ v (Q.coeff 0) := fun i => hgQ' ▸ v_coeff_le_gauss Q i
    obtain ⟨y, hy1, hygen⟩ := exists_generic (Z.val + P.roots + Q.roots)
    have hyZ : ∀ ζ ∈ Z, 1 ≤ v (y - ζ) := fun ζ hζ => hygen ζ (by simp [hζ]) (hZ ζ hζ).le
    have hyS : y ∈ S := hS y hy1 hyZ
    have hvP : v (P.eval y) = gauss P := v_eval_eq_gauss P hy1 fun α hα => hygen α (by simp [hα])
    have hvQ : v (Q.eval y) = gauss Q := v_eval_eq_gauss Q hy1 fun α hα => hygen α (by simp [hα])
    have hdiff : (r k).evalAt y - (r j).evalAt y = P.eval y / Q.eval y := by
      rw [hP, hQ]
      simp only [RatPair.evalAt, eval_sub, eval_mul]
      rw [div_sub_div _ _ (hpf k y hyS) (hpf j y hyS)]
      congr 1
      ring
    have hlt : gauss P < v e * gauss Q := by
      have := hN k hk j hj y hyS
      rwa [hdiff, map_div₀, hvP, hvQ, div_lt_iff₀ (gauss_pos hQne)] at this
    have hv0 : v (Q.coeff 0) ≠ 0 := by rwa [Ne, map_eq_zero]
    calc v (PowerSeries.coeff m (T P Q)) ≤ gauss P * (v (Q.coeff 0))⁻¹ := v_coeff_T_le P Q hQ0 hQcoef' m
      _ < v e * gauss Q * (v (Q.coeff 0))⁻¹ := mul_lt_mul_of_pos_right hlt (zero_lt_iff.2 (inv_ne_zero hv0))
      _ = v e := by rw [← hgQ', mul_assoc, mul_inv_cancel₀ (gauss_ne_zero hQne), mul_one]
  obtain ⟨N₁, hN₁⟩ := hA e₀ he₀
  obtain ⟨k₀, hk₀, hge⟩ := hfreq (max N₀ N₁)
  have hk₀N₀ : N₀ ≤ k₀ := (le_max_left _ _).trans hk₀
  have hk₀N₁ : N₁ ≤ k₀ := (le_max_right _ _).trans hk₀
  set M₀ : Γ₀ := gauss (r k₀).num / gauss (r k₀).den with hM₀
  have hve₀ : 0 < v e₀ := (Valuation.pos_iff _).2 he₀
  have hM₀pos : 0 < M₀ := hve₀.trans_le hge

  have hstab : ∀ k, N₀ ≤ k → gauss (r k).num / gauss (r k).den = M₀ := by
    intro k hk
    obtain ⟨y, hy1, hygen⟩ :=
      exists_generic (Z.val + ((r k).num.roots + (r k).den.roots) + ((r k₀).num.roots + (r k₀).den.roots))
    have hyZ : ∀ ζ ∈ Z, 1 ≤ v (y - ζ) := fun ζ hζ => hygen ζ (by simp [hζ]) (hZ ζ hζ).le
    have hyS : y ∈ S := hS y hy1 hyZ
    have hk' := hvalgen k y hy1 (fun b hb => hygen b (by
      rw [Multiset.mem_add, Multiset.mem_add]; exact Or.inl (Or.inr hb)))
    have hk₀' := hvalgen k₀ y hy1 (fun b hb => hygen b (by rw [Multiset.mem_add]; exact Or.inr hb))
    rw [← hk', hM₀, ← hk₀']
    have hdiff : v ((r k).evalAt y - (r k₀).evalAt y) < v ((r k₀).evalAt y) := by
      rw [hk₀']; exact (hN₀ k hk k₀ hk₀N₀ y hyS).trans_le hge
    have : (r k).evalAt y = (r k₀).evalAt y + ((r k).evalAt y - (r k₀).evalAt y) := by ring
    rw [this]
    exact Valuation.map_add_eq_of_lt_left _ hdiff

  have hcoefM : ∀ k, N₀ ≤ k → ∀ m, v (c k m) ≤ M₀ := by
    intro k hk m
    calc v (c k m) ≤ gauss (r k).num * (v ((r k).den.coeff 0))⁻¹ := v_coeff_T_le _ _ (hcoef0 k) (hQcoef k) m
      _ = gauss (r k).num / gauss (r k).den := by rw [← hgQ k, div_eq_mul_inv]
      _ = M₀ := hstab k hk

  have hnum0 : (r k₀).num ≠ 0 := by
    intro h
    apply hM₀pos.ne'
    show gauss (r k₀).num / gauss (r k₀).den = 0
    rw [h, gauss_zero, zero_div]
  have hq0pos : ∀ k, 0 < v ((r k).den.coeff 0) := fun k => (Valuation.pos_iff _).2 (hcoef0 k)
  have hD : ∃ ν : ℕ, v (c k₀ ν) = M₀ := by
    by_contra hno
    push Not at hno
    have hlt' : ∀ m, v (c k₀ m) < M₀ := fun m => lt_of_le_of_ne (hcoefM k₀ hk₀N₀ m) (hno m)
    have : gauss (r k₀).num < gauss (r k₀).num := by
      have hM₀q : M₀ * v ((r k₀).den.coeff 0) = gauss (r k₀).num := by
        show gauss (r k₀).num / gauss (r k₀).den * v ((r k₀).den.coeff 0) = gauss (r k₀).num
        rw [← hgQ k₀, div_mul_cancel₀ _ (gauss_ne_zero (hden_ne k₀))]
      refine gauss_lt (gauss_ne_zero hnum0) fun i => ?_
      rw [coeff_eq_sum_T _ _ (hcoef0 k₀) i, ← hM₀q]
      refine Valuation.map_sum_lt _ (mul_ne_zero hM₀pos.ne' (hq0pos k₀).ne') fun x _ => ?_
      rw [map_mul]
      calc v (PowerSeries.coeff x.1 (T (r k₀).num (r k₀).den)) * v ((r k₀).den.coeff x.2)
          ≤ v (c k₀ x.1) * v ((r k₀).den.coeff 0) := mul_le_mul_right (hQcoef k₀ x.2) _
        _ < M₀ * v ((r k₀).den.coeff 0) := mul_lt_mul_of_pos_right (hlt' x.1) (hq0pos k₀)
    exact lt_irrefl _ this
  obtain ⟨ν, hν₀⟩ := hD

  have hν : ∀ k, k₀ ≤ k → v (c k ν) = M₀ := by
    intro k hk
    have hdiff := hN₁ k (hk₀N₁.trans hk) k₀ hk₀N₁ ν
    have : c k ν = c k₀ ν + (c k ν - c k₀ ν) := by ring
    rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [hν₀]; exact hdiff.trans_le hge), hν₀]

  obtain ⟨y₀, hy₀1, hy₀gen⟩ := exists_generic (Z.val + ((r k₀).num.roots + (r k₀).den.roots))
  have hy₀Z : ∀ ζ ∈ Z, 1 ≤ v (y₀ - ζ) := fun ζ hζ => hy₀gen ζ (by simp [hζ]) (hZ ζ hζ).le
  set eM : K := (r k₀).evalAt y₀ with heM
  have hveM : v eM = M₀ := hvalgen k₀ y₀ hy₀1 (fun b hb => hy₀gen b (by rw [Multiset.mem_add]; exact Or.inr hb))
  have heM0 : eM ≠ 0 := (Valuation.ne_zero_iff _).1 (by rw [hveM]; exact hM₀pos.ne')

  refine ⟨f ⟨0, h0S⟩, hf0, fun y hy1 => ?_⟩
  by_contra hlt
  push Not at hlt
  set z : K := (y : K) with hzdef
  have hyS : z ∈ S := y.2
  have hz0 : z ≠ 0 := by
    intro hz
    have : y = ⟨0, h0S⟩ := Subtype.ext hz
    rw [this] at hlt
    exact lt_irrefl _ hlt
  have hvz : 0 < v z := (Valuation.pos_iff _).2 hz0
  have hfz0 : f y ≠ 0 := h0 y hy1

  obtain ⟨L₁, hL₁⟩ := hung (f y) hfz0
  set L : ℕ := max L₁ k₀ with hLdef
  have hLk₀ : k₀ ≤ L := le_max_right _ _
  have hLN₀ : N₀ ≤ L := hk₀N₀.trans hLk₀
  have hroot : ∀ l, L ≤ l → ∃ β : K, (r l).num.eval β = 0 ∧ v β ≤ v z := by
    intro l hl
    have herr := hL₁ l ((le_max_left _ _).trans hl)
    have hnum0 : (r l).num ≠ 0 := by
      intro hn
      have h1 := herr y
      have : (r l).evalAt z = 0 := by show (r l).num.eval z / (r l).den.eval z = 0; rw [hn, eval_zero, zero_div]
      rw [this, zero_sub, Valuation.map_neg] at h1
      exact lt_irrefl _ h1
    refine exists_root_of_v_eval_div_lt _ _ hnum0 (hroots l) hz0 hy1 ?_
    show v ((r l).evalAt z) < v ((r l).evalAt 0)
    have e1 : v ((r l).evalAt z) = v (f y) := by
      have : (r l).evalAt z = f y + ((r l).evalAt z - f y) := by ring
      rw [this]; exact Valuation.map_add_eq_of_lt_left _ (herr y)
    have e2 : v ((r l).evalAt 0) = v (f ⟨0, h0S⟩) := by
      have : (r l).evalAt 0 = f ⟨0, h0S⟩ + ((r l).evalAt 0 - f ⟨0, h0S⟩) := by ring
      rw [this]; exact Valuation.map_add_eq_of_lt_left _ ((herr ⟨0, h0S⟩).trans hlt)
    rw [e1, e2]; exact hlt

  have hnumval : ∀ l (w : K), v w < 1 →
      v ((r l).num.eval w) = v ((r l).evalAt w) * v ((r l).den.coeff 0) := by
    intro l w hw
    have hden : v ((r l).den.eval w) = v ((r l).den.coeff 0) := by
      rw [← hgQ l]
      refine v_eval_eq_gauss _ hw.le fun α hα hα1 => ?_
      have hα1' : v α = 1 := le_antisymm hα1 (hroots l α hα)
      rw [Valuation.map_sub_eq_of_lt_right _ (by rw [hα1']; exact hw), hα1']
    have : (r l).num.eval w = (r l).evalAt w * (r l).den.eval w := by
      rw [RatPair.evalAt, div_mul_cancel₀ _ (hpf l w (hS' w hw))]
    rw [this, map_mul, hden]

  have htrack : ∀ l l' : ℕ, L ≤ l → L ≤ l' → ∀ θ : K,
      (∀ w : ↥S, v ((r l').evalAt (w : K) - (r l).evalAt (w : K)) < v θ) → ∀ i : ℕ,
      v θ ≤ M₀ * v z ^ ν * (v z ^ i) ^ ν →
      ∀ α : K, (r l).num.eval α = 0 → v α ≤ v z →
      ∃ β : K, (r l').num.eval β = 0 ∧ v β ≤ v z ∧ v (α - β) ≤ v z * v z ^ i := by
    intro l l' hl hl' θ hθ i hθi α hαr hαz
    have hαS : α ∈ S := hS' α (hαz.trans_lt hy1)
    have hrα : (r l).evalAt α = 0 := by
      show (r l).num.eval α / (r l).den.eval α = 0; rw [hαr, zero_div]
    have hsmall : v ((r l').evalAt α) < v θ := by
      have := hθ ⟨α, hαS⟩; rwa [hrα, sub_zero] at this
    refine exists_root_v_sub_le _ _ (hcoef0 l') (hroots l') hz0 hy1 hM₀pos (hcoefM l' (hLN₀.trans hl')) ν
      (hν l' (hLk₀.trans hl')) (hroot l' hl') hαz (pow_le_one₀ zero_le' hy1.le) ?_
    rw [hnumval l' α (hαz.trans_lt hy1), mul_comm (M₀) (v ((r l').den.coeff 0)), mul_assoc, mul_assoc]
    rw [mul_comm (v ((r l').evalAt α))]
    refine mul_le_mul_right ?_ _
    rw [← mul_assoc]
    exact hsmall.le.trans hθi

  set θ : ℕ → K := fun i => eM * z ^ ν * (z ^ i) ^ ν with hθdef
  have hθ0 : ∀ i, θ i ≠ 0 := fun i => mul_ne_zero (mul_ne_zero heM0 (pow_ne_zero _ hz0)) (pow_ne_zero _ (pow_ne_zero _ hz0))
  have hvθ : ∀ i, v (θ i) = M₀ * v z ^ ν * (v z ^ i) ^ ν := fun i => by
    simp only [hθdef]; rw [map_mul, map_mul, map_pow, map_pow, map_pow, hveM]
  have hNf : ∀ i, ∃ N : ℕ, ∀ k ≥ N, ∀ w : ↥S, v ((r k).evalAt (w : K) - f w) < v (θ i) := fun i => hung (θ i) (hθ0 i)
  choose Nf hNf' using hNf
  let l : ℕ → ℕ := fun i => Nat.rec (max L (Nf 0)) (fun i li => max (li + 1) (Nf (i + 1))) i
  have hl0 : l 0 = max L (Nf 0) := rfl
  have hlsucc : ∀ i, l (i + 1) = max (l i + 1) (Nf (i + 1)) := fun i => rfl
  have hlL : ∀ i, L ≤ l i := by
    intro i; induction i with
    | zero => rw [hl0]; exact le_max_left _ _
    | succ i ih => rw [hlsucc]; exact ih.trans ((Nat.le_succ _).trans (le_max_left _ _))
  have hlN : ∀ i, Nf i ≤ l i := by
    intro i; cases i with
    | zero => rw [hl0]; exact le_max_right _ _
    | succ i => rw [hlsucc]; exact le_max_right _ _
  have hlmono : ∀ i, l i ≤ l (i + 1) := fun i => by rw [hlsucc]; exact (Nat.le_succ _).trans (le_max_left _ _)
  have hli : ∀ i, i ≤ l i := by
    intro i; induction i with
    | zero => exact Nat.zero_le _
    | succ i ih => rw [hlsucc]; exact (Nat.succ_le_succ ih).trans (le_max_left _ _)
  have hdiffl : ∀ i, ∀ w : ↥S, v ((r (l (i + 1))).evalAt (w : K) - (r (l i)).evalAt (w : K)) < v (θ i) := by
    intro i w
    have h1 := hNf' i (l (i + 1)) ((hlN i).trans (hlmono i)) w
    have h2 := hNf' i (l i) (hlN i) w
    have : (r (l (i + 1))).evalAt (w : K) - (r (l i)).evalAt (w : K)
        = ((r (l (i + 1))).evalAt (w : K) - f w) - ((r (l i)).evalAt (w : K) - f w) := by ring
    rw [this]; exact Valuation.map_sub_lt _ h1 h2

  let a : ∀ i : ℕ, {β : K // (r (l i)).num.eval β = 0 ∧ v β ≤ v z} := fun i =>
    Nat.rec (motive := fun i => {β : K // (r (l i)).num.eval β = 0 ∧ v β ≤ v z})
      ⟨Classical.choose (hroot (l 0) (hlL 0)), Classical.choose_spec (hroot (l 0) (hlL 0))⟩
      (fun i prev =>
        ⟨Classical.choose (htrack (l i) (l (i + 1)) (hlL i) (hlL (i + 1)) (θ i) (hdiffl i) i (hvθ i).le
            prev.1 prev.2.1 prev.2.2),
          (Classical.choose_spec (htrack (l i) (l (i + 1)) (hlL i) (hlL (i + 1)) (θ i) (hdiffl i) i (hvθ i).le
            prev.1 prev.2.1 prev.2.2)).1,
          (Classical.choose_spec (htrack (l i) (l (i + 1)) (hlL i) (hlL (i + 1)) (θ i) (hdiffl i) i (hvθ i).le
            prev.1 prev.2.1 prev.2.2)).2.1⟩) i

  have ha_succ : ∀ i, a (i + 1) =
      ⟨Classical.choose (htrack (l i) (l (i + 1)) (hlL i) (hlL (i + 1)) (θ i) (hdiffl i) i (hvθ i).le
          (a i).1 (a i).2.1 (a i).2.2),
        (Classical.choose_spec (htrack (l i) (l (i + 1)) (hlL i) (hlL (i + 1)) (θ i) (hdiffl i) i (hvθ i).le
          (a i).1 (a i).2.1 (a i).2.2)).1,
        (Classical.choose_spec (htrack (l i) (l (i + 1)) (hlL i) (hlL (i + 1)) (θ i) (hdiffl i) i (hvθ i).le
          (a i).1 (a i).2.1 (a i).2.2)).2.1⟩ := fun i => rfl
  have hclose : ∀ i, v ((a (i + 1)).1 - (a i).1) ≤ v z * v z ^ i := by
    intro i
    have hspec := (Classical.choose_spec (htrack (l i) (l (i + 1)) (hlL i) (hlL (i + 1)) (θ i) (hdiffl i) i
      (hvθ i).le (a i).1 (a i).2.1 (a i).2.2)).2.2
    rw [ha_succ i, Valuation.map_sub_swap]
    exact hspec

  have hca : CauchySeq (fun i => (a i).1) :=
    MMCplumb.cauchySeq_of_v_sub_succ_le hrk (fun i => (a i).1) z z hy1 hclose
  obtain ⟨x, hx, hxz⟩ := MMCplumb.exists_tendsto_of_cauchySeq_of_v_sub_le (fun i => (a i).1) hca 0 (v z)
    (fun i => by rw [sub_zero]; exact (a i).2.2)
  rw [sub_zero] at hxz
  have hx1 : v x < 1 := hxz.trans_lt hy1
  have hxS : x ∈ S := hS' x hx1
  have hfx : f ⟨x, hxS⟩ ≠ 0 := h0 ⟨x, hxS⟩ hx1
  set e : K := f ⟨x, hxS⟩ with hedef
  obtain ⟨Ne, hNe⟩ := hung e hfx
  have he' : e * z / eM ≠ 0 := div_ne_zero (mul_ne_zero hfx hz0) heM0
  obtain ⟨N', hN'⟩ := MMCplumb.exists_forall_v_sub_lt_of_tendsto (fun i => (a i).1) x hx (e * z / eM) he'
  set i : ℕ := max Ne N' with hidef
  have hli' : Ne ≤ l i := (le_max_left _ _).trans (hli i)
  have h1 : v ((r (l i)).evalAt x - e) < v e := hNe (l i) hli' ⟨x, hxS⟩

  have h2 : v ((r (l i)).evalAt x) < v e := by
    set B : K[X] := (r (l i)).num.comp (C z * X) with hBdef
    have hai := (a i).2
    have hnum0' : (r (l i)).num ≠ 0 := by
      intro hn
      have := hroot (l i) (hlL i)

      have herr := hL₁ (l i) ((le_max_left _ _).trans (hlL i)) y
      have : (r (l i)).evalAt z = 0 := by show (r (l i)).num.eval z / (r (l i)).den.eval z = 0; rw [hn, eval_zero, zero_div]
      rw [this, zero_sub, Valuation.map_neg] at herr
      exact lt_irrefl _ herr
    have hBne : B ≠ 0 := comp_C_mul_X_ne_zero hnum0' hz0
    have hx' : v (x / z) ≤ 1 := by rw [map_div₀, div_le_one₀ hvz]; exact hxz
    have hmem : (a i).1 / z ∈ rin B := by
      rw [rin, Multiset.mem_filter]
      refine ⟨(mem_roots hBne).2 ?_, ?_⟩
      · rw [IsRoot, hBdef, eval_comp_C_mul_X', mul_div_cancel₀ _ hz0]; exact hai.1
      · rw [map_div₀, div_le_one₀ hvz]; exact hai.2

    have hprod : ((rin B).map fun β => v (x / z - β)).prod ≤ v (x / z - (a i).1 / z) := by
      obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hmem
      rw [ht, Multiset.map_cons, Multiset.prod_cons]
      refine mul_le_of_le_one_right' ?_

      have : ∀ s : Multiset K, (∀ b ∈ s, v b ≤ 1) → (s.map fun β => v (x / z - β)).prod ≤ 1 := by
        intro s
        induction s using Multiset.induction_on with
        | empty => intro _; simp
        | cons b s ih =>
          intro hs
          rw [Multiset.map_cons, Multiset.prod_cons]
          refine mul_le_one' ?_ (ih fun b' hb' => hs b' (Multiset.mem_cons_of_mem hb'))
          exact (Valuation.map_sub _ _ _).trans (max_le hx' (hs b (Multiset.mem_cons_self _ _)))
      refine this t fun b hb => ?_
      have : b ∈ rin B := by rw [ht]; exact Multiset.mem_cons_of_mem hb
      rw [rin, Multiset.mem_filter] at this
      exact this.2
    have hgaussB : gauss B ≤ gauss (r (l i)).num := by
      refine gauss_le fun j => ?_
      rw [hBdef, comp_C_mul_X_coeff, map_mul, map_pow]
      exact (mul_le_of_le_one_right' (pow_le_one₀ zero_le' hy1.le)).trans (v_coeff_le_gauss _ j)
    have hgaussnum : gauss (r (l i)).num = M₀ * v ((r (l i)).den.coeff 0) := by
      rw [← hgQ (l i), ← hstab (l i) (hLN₀.trans (hlL i)), div_mul_cancel₀ _ (gauss_ne_zero (hden_ne (l i)))]
    have hnumx : v ((r (l i)).num.eval x) ≤ M₀ * v ((r (l i)).den.coeff 0) * (v (x - (a i).1) / v z) := by
      have e1 : (r (l i)).num.eval x = B.eval (x / z) := by rw [hBdef, eval_comp_C_mul_X', mul_div_cancel₀ _ hz0]
      rw [e1, v_eval_eq_gauss_mul_prod B hx', ← hgaussnum]
      refine mul_le_mul' hgaussB (hprod.trans ?_)
      rw [← sub_div, map_div₀]
    have hq0 : 0 < v ((r (l i)).den.coeff 0) := hq0pos (l i)
    have hrx : v ((r (l i)).evalAt x) * v ((r (l i)).den.coeff 0) = v ((r (l i)).num.eval x) :=
      (hnumval (l i) x hx1).symm
    have hdist : v (x - (a i).1) < v e * v z / M₀ := by
      have := hN' i (le_max_right _ _)
      rw [Valuation.map_sub_swap, map_div₀, map_mul, hveM] at this
      exact this

    have key : M₀ * (v (x - (a i).1) / v z) < v e := by
      have h' : v (x - (a i).1) / v z < v e / M₀ := by
        rw [div_lt_iff₀ hvz]
        calc v (x - (a i).1) < v e * v z / M₀ := hdist
          _ = v e / M₀ * v z := by rw [div_mul_eq_mul_div]
      calc M₀ * (v (x - (a i).1) / v z) < M₀ * (v e / M₀) := mul_lt_mul_of_pos_left h' hM₀pos
        _ = v e := by rw [mul_div_assoc', mul_div_cancel_left₀ _ hM₀pos.ne']
    have : v ((r (l i)).evalAt x) * v ((r (l i)).den.coeff 0) < v e * v ((r (l i)).den.coeff 0) := by
      rw [hrx]
      refine hnumx.trans_lt ?_
      rw [mul_assoc, mul_comm (v ((r (l i)).den.coeff 0)), ← mul_assoc]
      exact mul_lt_mul_of_pos_right key hq0
    exact lt_of_mul_lt_mul_right' this
  have : v e < v e := by
    have ee : e = (r (l i)).evalAt x - ((r (l i)).evalAt x - e) := by ring
    conv_lhs => rw [ee]
    exact Valuation.map_sub_lt _ h2 h1
  exact lt_irrefl _ this

end ZM0

end IdDisc

namespace IdDisc

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

section ZMgen

variable [IsAlgClosed K]

open scoped Classical

theorem zm [CompleteSpace K]
    (hrk : ∀ x y : K, v x < 1 → y ≠ 0 → ∃ n : ℕ, v x ^ n ≤ v y)
    (S : Set K) (a π : K) (hπ : π ≠ 0) (Z : Finset K) (hZ : ∀ ζ ∈ Z, v (a - ζ) = v π)
    (hS : ∀ z : K, v (z - a) ≤ v π → (∀ ζ ∈ Z, v π ≤ v (z - ζ)) → z ∈ S)
    {f : ↥S → K} (hf : f ∈ holOn K S)
    (h0 : ∀ z : ↥S, v ((z : K) - a) < v π → f z ≠ 0) :
    ∃ δ : K, δ ≠ 0 ∧ ∀ z : ↥S, v ((z : K) - a) < v π → v δ ≤ v (f z) := by
  have hvπ : 0 < v π := (Valuation.pos_iff _).2 hπ
  let S' : Set K := {y | π * y + a ∈ S}
  let ι : ↥S' → ↥S := fun y => ⟨π * (y : K) + a, y.2⟩
  let f' : ↥S' → K := fun y => f (ι y)
  let Z' : Finset K := Z.image fun ζ => (ζ - a) / π
  have key_sub : ∀ y ζ : K, π * y + a - ζ = π * (y - (ζ - a) / π) := fun y ζ => by
    field_simp
    ring
  have hZ' : ∀ ζ' ∈ Z', v ζ' = 1 := fun ζ' hζ' => by
    obtain ⟨ζ, hζ, rfl⟩ := Finset.mem_image.1 hζ'
    rw [map_div₀, div_eq_one_iff_eq hvπ.ne', ← Valuation.map_neg, neg_sub]
    exact hZ ζ hζ
  have hS'' : ∀ y : K, v y ≤ 1 → (∀ ζ' ∈ Z', 1 ≤ v (y - ζ')) → y ∈ S' := fun y hy hyZ => by
    show π * y + a ∈ S
    refine hS _ ?_ fun ζ hζ => ?_
    · rw [add_sub_cancel_right, map_mul]; exact mul_le_of_le_one_right' hy
    · rw [key_sub, map_mul]
      exact le_mul_of_one_le_right' (hyZ _ (Finset.mem_image_of_mem _ hζ))
  have hf' : f' ∈ holOn K S' := by
    obtain ⟨r, hpf, ⟨b, hb⟩, hlim⟩ := hf
    refine ⟨fun k => aff a π (r k), fun k y hy => ?_, ⟨b, fun k y => ?_⟩, ?_⟩
    · show (aff a π (r k)).den.eval y ≠ 0
      rw [aff_den_eval]; exact hpf k _ hy
    · show v ((aff a π (r k)).evalAt (y : K)) ≤ v b
      rw [aff_evalAt]; exact hb k (ι y)
    · have heq : (fun k (y : ↥S') => (aff a π (r k)).evalAt (y : K))
          = fun k => (fun z : ↥S => (r k).evalAt (z : K)) ∘ ι := by
        funext k y
        show (aff a π (r k)).evalAt (y : K) = (r k).evalAt (π * (y : K) + a)
        exact aff_evalAt a π (r k) y
      show TendstoUniformly (fun k (y : ↥S') => (aff a π (r k)).evalAt (y : K)) f' Filter.atTop
      rw [heq]
      exact hlim.comp ι
  have hpre : ∀ z : ↥S, π * (((z : K) - a) / π) + a = (z : K) := fun z => by
    rw [mul_div_assoc', mul_div_cancel_left₀ _ hπ, sub_add_cancel]
  have hpreS : ∀ z : ↥S, ((z : K) - a) / π ∈ S' := fun z => by
    show π * (((z : K) - a) / π) + a ∈ S
    rw [hpre z]; exact z.2
  have hιpre : ∀ z : ↥S, ι ⟨((z : K) - a) / π, hpreS z⟩ = z := fun z => Subtype.ext (hpre z)
  have h0' : ∀ y : ↥S', v (y : K) < 1 → f' y ≠ 0 := fun y hy => by
    show f (ι y) ≠ 0
    refine h0 (ι y) ?_
    show v (π * (y : K) + a - a) < v π
    rw [add_sub_cancel_right, map_mul]
    calc v π * v (y : K) < v π * 1 := mul_lt_mul_of_pos_left hy hvπ
      _ = v π := mul_one _
  obtain ⟨δ, hδ0, hδ⟩ := zm0 hrk S' Z' hZ' hS'' hf' h0'
  refine ⟨δ, hδ0, fun z hz => ?_⟩
  have hy1 : v (((z : K) - a) / π) < 1 := by rw [map_div₀, div_lt_one₀ hvπ]; exact hz
  have := hδ ⟨((z : K) - a) / π, hpreS z⟩ hy1
  simp only [f'] at this
  rwa [hιpre z] at this

end ZMgen

end IdDisc

end

open CerednikDrinfeld.Omega in

theorem solution
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (S : Set K) (a π : K) (hπ : π ≠ 0) (Z : Finset K) (hZ : ∀ ζ ∈ Z, Valued.v (a - ζ) = Valued.v π)
    (hS : ∀ z : K, Valued.v (z - a) ≤ Valued.v π → (∀ ζ ∈ Z, Valued.v π ≤ Valued.v (z - ζ)) → z ∈ S)
    {f : ↥S → K} (hf : f ∈ holOn K S)
    (h0 : ∀ z : ↥S, Valued.v ((z : K) - a) < Valued.v π → f z ≠ 0) :
    ∃ δ : K, δ ≠ 0 ∧ ∀ z : ↥S, Valued.v ((z : K) - a) < Valued.v π → Valued.v δ ≤ Valued.v (f z) :=
  IdDisc.zm hrk S a π hπ Z hZ hS hf h0

end S_CerednikDrinfeld_Omega_exists_forall_le_v_apply_of_v_sub_lt_of_forall_ne_zero
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_forall_le_v_apply_of_v_sub_lt_of_forall_ne_zero (solution)
