-- Prove2me | solution 1 for CerednikDrinfeld.Omega.RatPair.identityPrinciple_disc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/711292d4-89aa-54ee-9b2c-b85bb5fac5ae

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_RatPair_identityPrinciple_disc

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

section L0

variable [IsAlgClosed K]

theorem L0 (S : Set K) (r : ℕ → RatPair K) (hpf : ∀ k, (r k).IsPoleFreeOn S)
    (Z : Finset K) (hZ : ∀ ζ ∈ Z, 1 ≤ v ζ)
    (hS : ∀ y : K, v y ≤ 1 → (∀ ζ ∈ Z, 1 ≤ v (y - ζ)) → y ∈ S)
    (hC : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ y ∈ S, v ((r k).evalAt y - (r j).evalAt y) < v e)
    (δ : K) (hδ : δ ≠ 0)
    (h0 : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y ∈ S, v y ≤ v δ → v ((r k).evalAt y) < v e) :
    ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y ∈ S, v y ≤ 1 → (∀ ζ ∈ Z, 1 ≤ v (y - ζ)) →
      v ((r k).evalAt y) < v e := by

  by_cases hδ1 : 1 ≤ v δ
  · intro e he
    obtain ⟨N, hN⟩ := h0 e he
    exact ⟨N, fun k hk y hy hy1 _ => hN k hk y hy (hy1.trans hδ1)⟩
  push Not at hδ1

  have hS' : ∀ y : K, v y < 1 → y ∈ S := fun y hy => hS y hy.le fun ζ hζ => by
    rw [Valuation.map_sub_eq_of_lt_right _ (hy.trans_le (hZ ζ hζ))]
    exact hZ ζ hζ

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

  let b : ℕ → ℕ → K := fun k m => PowerSeries.coeff m (T (r k).num (r k).den)

  have hA : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ m, v (b k m - b j m) < v e := by
    intro e he
    obtain ⟨N, hN⟩ := hC e he
    refine ⟨N, fun k hk j hj m => ?_⟩
    set P := (r k).num * (r j).den - (r j).num * (r k).den with hP
    set Q := (r k).den * (r j).den with hQ
    have hQ0 : Q.coeff 0 ≠ 0 := by rw [hQ, mul_coeff_zero]; exact mul_ne_zero (hcoef0 k) (hcoef0 j)
    have hQne : Q ≠ 0 := mul_ne_zero (hden_ne k) (hden_ne j)
    have hbT : b k m - b j m = PowerSeries.coeff m (T P Q) := by
      simp only [b]; rw [hP, hQ, T_sub _ _ _ _ (hcoef0 k) (hcoef0 j), map_sub]
    rw [hbT]
    have hQroots : ∀ α ∈ Q.roots, 1 ≤ v α := fun α hα => by
      rw [hQ, roots_mul hQne, Multiset.mem_add] at hα
      rcases hα with hα | hα
      · exact hroots k α hα
      · exact hroots j α hα
    have hgQ : gauss Q = v (Q.coeff 0) := gauss_eq_coeff_zero_of_roots Q hQroots
    have hQcoef : ∀ i, v (Q.coeff i) ≤ v (Q.coeff 0) := fun i => hgQ ▸ v_coeff_le_gauss Q i

    obtain ⟨y, hy1, hygen⟩ := exists_generic (Z.val + P.roots + Q.roots)
    have hyZ : ∀ ζ ∈ Z, 1 ≤ v (y - ζ) := fun ζ hζ => by
      rcases le_or_gt (v ζ) 1 with h | h
      · exact hygen ζ (by simp [hζ]) h
      · rw [Valuation.map_sub_eq_of_lt_right _ (hy1.trans_lt h)]; exact h.le
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
    calc v (PowerSeries.coeff m (T P Q)) ≤ gauss P * (v (Q.coeff 0))⁻¹ := v_coeff_T_le P Q hQ0 hQcoef m
      _ < v e * gauss Q * (v (Q.coeff 0))⁻¹ := mul_lt_mul_of_pos_right hlt (zero_lt_iff.2 (inv_ne_zero hv0))
      _ = v e := by rw [← hgQ, mul_assoc, mul_inv_cancel₀ (gauss_ne_zero hQne), mul_one]

  have hB : ∀ m, ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, v (b k m) < v e := by
    intro m e he
    obtain ⟨N, hN⟩ := h0 (e * δ ^ m) (mul_ne_zero he (pow_ne_zero _ hδ))
    refine ⟨N, fun k hk => ?_⟩
    set P := (r k).num.comp (C δ * X) with hP
    set Q := (r k).den.comp (C δ * X) with hQ
    have hQ0' : Q.coeff 0 = (r k).den.coeff 0 := by rw [hQ, comp_C_mul_X_coeff, pow_zero, mul_one]
    have hQ0 : Q.coeff 0 ≠ 0 := by rw [hQ0']; exact hcoef0 k
    have hQne : Q ≠ 0 := fun h => hQ0 (by rw [h, coeff_zero])
    have hQeval : ∀ y, Q.eval y = (r k).den.eval (δ * y) := fun y => by
      rw [hQ, eval_comp, eval_mul, eval_C, eval_X]
    have hPeval : ∀ y, P.eval y = (r k).num.eval (δ * y) := fun y => by
      rw [hP, eval_comp, eval_mul, eval_C, eval_X]
    have hQroots : ∀ α ∈ Q.roots, 1 ≤ v α := fun α hα => by
      have hr : (r k).den.eval (δ * α) = 0 := by rw [← hQeval]; exact (mem_roots hQne).1 hα
      by_contra hlt
      push Not at hlt
      refine hpf k (δ * α) (hS' _ ?_) hr
      rw [map_mul]
      exact (mul_le_mul' le_rfl hlt.le).trans_lt (by rwa [mul_one])
    have hgQ : gauss Q = v (Q.coeff 0) := gauss_eq_coeff_zero_of_roots Q hQroots
    have hQcoef : ∀ i, v (Q.coeff i) ≤ v (Q.coeff 0) := fun i => hgQ ▸ v_coeff_le_gauss Q i
    obtain ⟨y, hy1, hygen⟩ := exists_generic (P.roots + Q.roots)
    have hvP : v (P.eval y) = gauss P := v_eval_eq_gauss P hy1 fun α hα => hygen α (by simp [hα])
    have hvQ : v (Q.eval y) = gauss Q := v_eval_eq_gauss Q hy1 fun α hα => hygen α (by simp [hα])
    have hyv : v (δ * y) ≤ v δ := by rw [map_mul]; exact mul_le_of_le_one_right' hy1
    have hyS : δ * y ∈ S := hS' _ (hyv.trans_lt hδ1)
    have hval : (r k).evalAt (δ * y) = P.eval y / Q.eval y := by rw [hPeval, hQeval]; rfl
    have hlt : gauss P < v (e * δ ^ m) * gauss Q := by
      have := hN k hk (δ * y) hyS hyv
      rwa [hval, map_div₀, hvP, hvQ, div_lt_iff₀ (gauss_pos hQne)] at this
    have hcoefT : PowerSeries.coeff m (T P Q) = b k m * δ ^ m := by
      simp only [b]; rw [hP, hQ]; exact T_comp_C_mul_X _ _ δ (hcoef0 k) m
    have hv0 : v (Q.coeff 0) ≠ 0 := by rwa [Ne, map_eq_zero]
    have h1 : v (b k m * δ ^ m) < v (e * δ ^ m) := by
      rw [← hcoefT]
      calc v (PowerSeries.coeff m (T P Q)) ≤ gauss P * (v (Q.coeff 0))⁻¹ := v_coeff_T_le P Q hQ0 hQcoef m
        _ < v (e * δ ^ m) * gauss Q * (v (Q.coeff 0))⁻¹ :=
          mul_lt_mul_of_pos_right hlt (zero_lt_iff.2 (inv_ne_zero hv0))
        _ = v (e * δ ^ m) := by rw [← hgQ, mul_assoc, mul_inv_cancel₀ (gauss_ne_zero hQne), mul_one]
    rw [map_mul, map_mul] at h1
    exact lt_of_mul_lt_mul_right' h1

  have hAB : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ m, v (b k m) < v e := by
    intro e he
    obtain ⟨N, hN⟩ := hA e he
    refine ⟨N, fun k hk m => ?_⟩
    obtain ⟨N', hN'⟩ := hB m e he
    have h1 := hN k hk (max N N') (le_max_left _ _) m
    have h2 := hN' (max N N') (le_max_right _ _)
    have : b k m = (b k m - b (max N N') m) + b (max N N') m := by ring
    rw [this]
    exact Valuation.map_add_lt _ h1 h2

  intro e he
  obtain ⟨N, hN⟩ := hAB e he
  refine ⟨N, fun k hk y _ hy1 hyZ => ?_⟩
  have hvQ : v ((r k).den.eval y) = gauss (r k).den := v_eval_eq_gauss _ hy1 (hrootsZ k y hy1 hyZ)
  have hvP : v ((r k).num.eval y) ≤ gauss (r k).num := v_eval_le_gauss _ hy1
  have hgauss : gauss (r k).num < v e * gauss (r k).den :=
    gauss_lt_of_coeff_T_lt _ _ (hcoef0 k) (hden_ne k) ((Valuation.ne_zero_iff _).2 he) (hN k hk)
  show v ((r k).num.eval y / (r k).den.eval y) < v e
  rw [map_div₀, hvQ, div_lt_iff₀ (gauss_pos (hden_ne k))]
  exact hvP.trans_lt hgauss

end L0

end IdDisc

namespace IdDisc

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

theorem L [IsAlgClosed K] (S : Set K) (r : ℕ → RatPair K) (hpf : ∀ k, (r k).IsPoleFreeOn S)
    (c π : K) (hπ : π ≠ 0) (Z : Finset K) (hZ : ∀ ζ ∈ Z, v π ≤ v (c - ζ))
    (hS : ∀ z : K, v (z - c) ≤ v π → (∀ ζ ∈ Z, v π ≤ v (z - ζ)) → z ∈ S)
    (hC : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ z ∈ S, v ((r k).evalAt z - (r j).evalAt z) < v e)
    (δ : K) (hδ : δ ≠ 0)
    (h0 : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z ∈ S, v (z - c) ≤ v δ → v ((r k).evalAt z) < v e) :
    ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z ∈ S, v (z - c) ≤ v π → (∀ ζ ∈ Z, v π ≤ v (z - ζ)) →
      v ((r k).evalAt z) < v e := by
  classical
  have hvπ : 0 < v π := (Valuation.pos_iff _).2 hπ
  have hvπ0 : v π ≠ 0 := hvπ.ne'

  let S' : Set K := {y | π * y + c ∈ S}
  let r' : ℕ → RatPair K := fun k => aff c π (r k)
  let Z' : Finset K := Z.image fun ζ => (ζ - c) / π
  have key_sub : ∀ y ζ : K, π * y + c - ζ = π * (y - (ζ - c) / π) := fun y ζ => by
    field_simp
    ring
  have hpf' : ∀ k, (r' k).IsPoleFreeOn S' := fun k y hy => by
    show (aff c π (r k)).den.eval y ≠ 0
    rw [aff_den_eval]; exact hpf k _ hy
  have hZ' : ∀ ζ' ∈ Z', 1 ≤ v ζ' := fun ζ' hζ' => by
    obtain ⟨ζ, hζ, rfl⟩ := Finset.mem_image.1 hζ'
    rw [map_div₀, le_div_iff₀ hvπ, one_mul, ← neg_sub, Valuation.map_neg]
    exact hZ ζ hζ
  have hS'' : ∀ y : K, v y ≤ 1 → (∀ ζ' ∈ Z', 1 ≤ v (y - ζ')) → y ∈ S' := fun y hy hyZ => by
    show π * y + c ∈ S
    refine hS _ ?_ fun ζ hζ => ?_
    · rw [add_sub_cancel_right, map_mul]; exact mul_le_of_le_one_right' hy
    · rw [key_sub, map_mul]
      exact le_mul_of_one_le_right' (hyZ _ (Finset.mem_image_of_mem _ hζ))
  have hC' : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ y ∈ S',
      v ((r' k).evalAt y - (r' j).evalAt y) < v e := fun e he => by
    obtain ⟨N, hN⟩ := hC e he
    refine ⟨N, fun k hk j hj y hy => ?_⟩
    show v ((aff c π (r k)).evalAt y - (aff c π (r j)).evalAt y) < v e
    rw [aff_evalAt, aff_evalAt]; exact hN k hk j hj _ hy
  have hδ' : δ / π ≠ 0 := div_ne_zero hδ hπ
  have h0' : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y ∈ S', v y ≤ v (δ / π) → v ((r' k).evalAt y) < v e :=
    fun e he => by
    obtain ⟨N, hN⟩ := h0 e he
    refine ⟨N, fun k hk y hy hyδ => ?_⟩
    show v ((aff c π (r k)).evalAt y) < v e
    rw [aff_evalAt]
    refine hN k hk _ hy ?_
    rw [add_sub_cancel_right, map_mul]
    rw [map_div₀, le_div_iff₀ hvπ, mul_comm] at hyδ
    exact hyδ
  have main := L0 S' r' hpf' Z' hZ' hS'' hC' (δ / π) hδ' h0'
  intro e he
  obtain ⟨N, hN⟩ := main e he
  refine ⟨N, fun k hk z hz hzc hzZ => ?_⟩
  set y := (z - c) / π with hy
  have hzy : π * y + c = z := by rw [hy]; field_simp; ring
  have hyS : y ∈ S' := by show π * y + c ∈ S; rw [hzy]; exact hz
  have hy1 : v y ≤ 1 := by rw [hy, map_div₀, div_le_iff₀ hvπ, one_mul]; exact hzc
  have hyZ : ∀ ζ' ∈ Z', 1 ≤ v (y - ζ') := fun ζ' hζ' => by
    obtain ⟨ζ, hζ, rfl⟩ := Finset.mem_image.1 hζ'
    rw [hy, ← sub_div, sub_sub_sub_cancel_right, map_div₀, le_div_iff₀ hvπ, one_mul]
    exact hzZ ζ hζ
  have := hN k hk y hyS hy1 hyZ
  rwa [show (r' k).evalAt y = (r k).evalAt z from by rw [← hzy]; exact aff_evalAt c π (r k) y] at this

end IdDisc

end

open CerednikDrinfeld.Omega in
theorem solution
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (S : Set K) (r : ℕ → RatPair K) (hr : ∀ k, (r k).IsPoleFreeOn S)
    (c π : K) (hπ : π ≠ 0) (Z : Finset K) (hZ : ∀ ζ ∈ Z, Valued.v π ≤ Valued.v (c - ζ))
    (hS : ∀ z : K, Valued.v (z - c) ≤ Valued.v π → (∀ ζ ∈ Z, Valued.v π ≤ Valued.v (z - ζ)) → z ∈ S)
    (hC : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ z ∈ S,
      Valued.v ((r k).evalAt z - (r j).evalAt z) < Valued.v e)
    (δ : K) (hδ : δ ≠ 0)
    (h0 : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z ∈ S, Valued.v (z - c) ≤ Valued.v δ →
      Valued.v ((r k).evalAt z) < Valued.v e) :
    ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z : K, Valued.v (z - c) ≤ Valued.v π →
      (∀ ζ ∈ Z, Valued.v π ≤ Valued.v (z - ζ)) → Valued.v ((r k).evalAt z) < Valued.v e := by
  intro e he
  obtain ⟨N, hN⟩ := IdDisc.L S r hr c π hπ Z hZ hS hC δ hδ h0 e he
  exact ⟨N, fun k hk z hz hzZ => hN k hk z (hS z hz hzZ) hz hzZ⟩

end S_CerednikDrinfeld_Omega_RatPair_identityPrinciple_disc
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_RatPair_identityPrinciple_disc (solution)
