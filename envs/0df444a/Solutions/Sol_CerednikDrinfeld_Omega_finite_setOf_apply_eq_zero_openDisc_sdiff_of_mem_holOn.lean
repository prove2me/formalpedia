-- Prove2me | solution 1 for CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_openDisc_sdiff_of_mem_holOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c9041a4e-3bbd-59b5-ba9f-e7d70f67070f

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Theorems.Thm_Polynomial_coeff_countP_roots_isDominant_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_Omega_exists_forall_v_apply_eq_on_circle_of_mem_holOn
import Theorems.Thm_CerednikDrinfeld_Omega_exists_mem_holOn_eq_sub_mul_of_apply_eq_zero
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_openDisc_sdiff_of_mem_holOn

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial Filter
open CerednikDrinfeld.Omega

namespace P2mKcRimCount

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

theorem gauss_eq_zero_iff {P : K[X]} : gauss P = 0 ↔ P = 0 :=
  ⟨fun h => by_contra fun hP => gauss_ne_zero hP h, fun h => by rw [h, gauss_zero]⟩

theorem gauss_C (a : K) : gauss (C a : K[X]) = v a := by
  apply le_antisymm
  · exact gauss_le fun i => by
      rw [coeff_C]; split_ifs
      · exact le_rfl
      · rw [map_zero]; exact zero_le'
  · simpa using v_coeff_le_gauss (C a) 0

theorem gauss_add_le (P Q : K[X]) : gauss (P + Q) ≤ max (gauss P) (gauss Q) :=
  gauss_le fun i => by
    rw [coeff_add]
    exact (Valuation.map_add _ _ _).trans (max_le_max (v_coeff_le_gauss P i) (v_coeff_le_gauss Q i))

theorem gauss_add_eq_of_lt {P Q : K[X]} (h : gauss Q < gauss P) : gauss (P + Q) = gauss P := by
  apply le_antisymm ((gauss_add_le P Q).trans (max_le le_rfl h.le))
  have hP : P ≠ 0 := by rintro rfl; rw [gauss_zero] at h; exact not_lt_of_ge zero_le' h
  obtain ⟨i, -, hi⟩ := exists_eq_gauss hP
  have hlt : v (Q.coeff i) < v (P.coeff i) := (v_coeff_le_gauss Q i).trans_lt (hi ▸ h)
  calc gauss P = v ((P + Q).coeff i) := by rw [coeff_add, Valuation.map_add_eq_of_lt_left _ hlt, hi]
    _ ≤ gauss (P + Q) := v_coeff_le_gauss _ _

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
  · classical
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
    · rw [max_eq_left hα, mul_one]
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
    · rw [max_eq_right hα.le]
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

end AlgClosed

def Nle (P : K[X]) : ℕ := P.roots.countP fun α => Valued.v α ≤ 1

def Nlt (P : K[X]) : ℕ := P.roots.countP fun α => Valued.v α < 1

section Rouche

variable [IsAlgClosed K]

theorem dominant {P : K[X]} (hP : P ≠ 0) :
    (v (P.coeff (Nle P)) = gauss P ∧ ∀ j, Nle P < j → v (P.coeff j) < gauss P) ∧
      (v (P.coeff (Nlt P)) = gauss P ∧ ∀ j, j < Nlt P → v (P.coeff j) < gauss P) := by
  obtain ⟨⟨hM, hM'⟩, ⟨hm, hm'⟩⟩ := Polynomial.coeff_countP_roots_isDominant_of_isAlgClosed K P hP
  have hGM : v (P.coeff (Nle P)) = gauss P := le_antisymm (v_coeff_le_gauss _ _) (gauss_le hM)
  have hGm : v (P.coeff (Nlt P)) = gauss P := le_antisymm (v_coeff_le_gauss _ _) (gauss_le hm)
  exact ⟨⟨hGM, fun j hj => hGM ▸ hM' j hj⟩, ⟨hGm, fun j hj => hGm ▸ hm' j hj⟩⟩

theorem rouche {P g : K[X]} (hP : P ≠ 0) (hg : gauss g < gauss P) :
    Nle (P + g) = Nle P ∧ Nlt (P + g) = Nlt P := by
  have hG : gauss (P + g) = gauss P := gauss_add_eq_of_lt hg
  have hPg : P + g ≠ 0 := fun h => by rw [h, gauss_zero] at hG; exact gauss_ne_zero hP hG.symm

  have hdom : ∀ j, v (P.coeff j) = gauss P → v ((P + g).coeff j) = gauss P := fun j hj => by
    rw [coeff_add, Valuation.map_add_eq_of_lt_left _ (by rw [hj]; exact (v_coeff_le_gauss g j).trans_lt hg), hj]
  have hsub : ∀ j, v (P.coeff j) < gauss P → v ((P + g).coeff j) < gauss P := fun j hj => by
    rw [coeff_add]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hj ((v_coeff_le_gauss g j).trans_lt hg))
  obtain ⟨⟨hM, hM'⟩, ⟨hm, hm'⟩⟩ := dominant hP
  obtain ⟨⟨kM, kM'⟩, ⟨km, km'⟩⟩ := dominant hPg
  rw [hG] at kM kM' km km'
  constructor
  ·
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (kM' _ h).ne (hdom _ hM)
    · have := hM' _ h

      exact (hsub _ this).ne kM
  · by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hm' _ h
      exact (hsub _ this).ne km
    · exact (km' _ h).ne (hdom _ hm)

end Rouche

theorem Nle_mul {P Q : K[X]} (h : P * Q ≠ 0) : Nle (P * Q) = Nle P + Nle Q := by
  rw [Nle, roots_mul h, Multiset.countP_add]; rfl

theorem Nlt_mul {P Q : K[X]} (h : P * Q ≠ 0) : Nlt (P * Q) = Nlt P + Nlt Q := by
  rw [Nlt, roots_mul h, Multiset.countP_add]; rfl

def scl (c R : K) (P : K[X]) : K[X] := P.comp (C c + C R * X)

theorem eval_scl (c R : K) (P : K[X]) (y : K) : (scl c R P).eval y = P.eval (c + R * y) := by
  simp [scl, eval_comp]

theorem eval_scl_hat (c : K) {R : K} (hR : R ≠ 0) (P : K[X]) (z : K) :
    (scl c R P).eval ((z - c) / R) = P.eval z := by
  rw [eval_scl, mul_div_cancel₀ _ hR, add_sub_cancel]

theorem scl_add (c R : K) (P Q : K[X]) : scl c R (P + Q) = scl c R P + scl c R Q := add_comp
theorem scl_sub (c R : K) (P Q : K[X]) : scl c R (P - Q) = scl c R P - scl c R Q := sub_comp
theorem scl_mul (c R : K) (P Q : K[X]) : scl c R (P * Q) = scl c R P * scl c R Q := mul_comp _ _ _

def hat (c R : K) (α : K) : K := (α - c) / R

theorem X_sub_C_comp (c : K) {R : K} (hR : R ≠ 0) (α : K) :
    (X - C α).comp (C c + C R * X) = C R * (X - C (hat c R α)) := by
  rw [sub_comp, X_comp, C_comp, hat, mul_sub, ← C_mul, mul_div_cancel₀ _ hR, C_sub]; ring

theorem roots_C_mul_prod_hat {R : K} (hR : R ≠ 0) (c : K) {a : K} (ha : a ≠ 0) (s : Multiset K) :
    (C a * (s.map fun α => C R * (X - C (hat c R α))).prod).roots = s.map (hat c R) := by
  induction s using Multiset.induction generalizing a with
  | empty => simp
  | cons α s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons,
      show C a * (C R * (X - C (hat c R α)) * (s.map fun α => C R * (X - C (hat c R α))).prod) =
        (X - C (hat c R α)) * (C (a * R) * (s.map fun α => C R * (X - C (hat c R α))).prod) by
          rw [C_mul]; ring]
    have hne : C (a * R) * (s.map fun α => C R * (X - C (hat c R α))).prod ≠ 0 := by
      refine mul_ne_zero (C_ne_zero.2 (mul_ne_zero ha hR)) (Multiset.prod_ne_zero fun h => ?_)
      obtain ⟨β, -, hβ⟩ := Multiset.mem_map.1 h
      exact mul_ne_zero (C_ne_zero.2 hR) (X_sub_C_ne_zero _) hβ
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero _) hne), roots_X_sub_C, ih (mul_ne_zero ha hR),
      Multiset.singleton_add]

section SclAlgClosed

variable [IsAlgClosed K]

theorem scl_eq (c : K) {R : K} (hR : R ≠ 0) (P : K[X]) :
    scl c R P = C P.leadingCoeff * (P.roots.map fun α => C R * (X - C (hat c R α))).prod := by
  conv_lhs => rw [scl, eq_C_mul_prod P]
  rw [mul_comp, C_comp, multiset_prod_comp, Multiset.map_map]
  congr 2
  refine Multiset.map_congr rfl fun α _ => ?_
  exact X_sub_C_comp c hR α

theorem roots_scl (c : K) {R : K} (hR : R ≠ 0) {P : K[X]} (hP : P ≠ 0) :
    (scl c R P).roots = P.roots.map (hat c R) := by
  rw [scl_eq c hR P, roots_C_mul_prod_hat hR c (leadingCoeff_ne_zero.2 hP)]

theorem scl_ne_zero (c : K) {R : K} (hR : R ≠ 0) {P : K[X]} (hP : P ≠ 0) : scl c R P ≠ 0 := by
  rw [scl_eq c hR P]
  refine mul_ne_zero (C_ne_zero.2 (leadingCoeff_ne_zero.2 hP)) (Multiset.prod_ne_zero fun h => ?_)
  obtain ⟨β, -, hβ⟩ := Multiset.mem_map.1 h
  exact mul_ne_zero (C_ne_zero.2 hR) (X_sub_C_ne_zero _) hβ

def Ncl (c R : K) (P : K[X]) : ℕ := P.roots.countP fun α => Valued.v (α - c) ≤ Valued.v R

def Nop (c R : K) (P : K[X]) : ℕ := P.roots.countP fun α => Valued.v (α - c) < Valued.v R

omit [IsAlgClosed K] in
theorem v_hat (c : K) {R : K} (hR : R ≠ 0) (α : K) : v (hat c R α) = v (α - c) / v R := map_div₀ _ _ _

omit [IsAlgClosed K] in
theorem v_hat_le_one_iff (c : K) {R : K} (hR : R ≠ 0) (α : K) : v (hat c R α) ≤ 1 ↔ v (α - c) ≤ v R := by
  rw [v_hat c hR, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hR))]

omit [IsAlgClosed K] in
theorem v_hat_lt_one_iff (c : K) {R : K} (hR : R ≠ 0) (α : K) : v (hat c R α) < 1 ↔ v (α - c) < v R := by
  rw [v_hat c hR, div_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hR))]

theorem Ncl_eq (c : K) {R : K} (hR : R ≠ 0) {P : K[X]} (hP : P ≠ 0) : Ncl c R P = Nle (scl c R P) := by
  rw [Nle, roots_scl c hR hP, Multiset.countP_map, ← Multiset.countP_eq_card_filter, Ncl]
  exact Multiset.countP_congr rfl fun α _ => by rw [v_hat_le_one_iff c hR]

theorem Nop_eq (c : K) {R : K} (hR : R ≠ 0) {P : K[X]} (hP : P ≠ 0) : Nop c R P = Nlt (scl c R P) := by
  rw [Nlt, roots_scl c hR hP, Multiset.countP_map, ← Multiset.countP_eq_card_filter, Nop]
  exact Multiset.countP_congr rfl fun α _ => by rw [v_hat_lt_one_iff c hR]

theorem rouche_at (c : K) {R : K} (hR : R ≠ 0) {P g : K[X]} (hP : P ≠ 0)
    (hg : gauss (scl c R g) < gauss (scl c R P)) :
    Ncl c R (P + g) = Ncl c R P ∧ Nop c R (P + g) = Nop c R P := by
  have hsP : scl c R P ≠ 0 := scl_ne_zero c hR hP
  have h := rouche hsP hg
  rw [← scl_add] at h
  have hPg : P + g ≠ 0 := by
    intro h0
    have h1 : gauss (scl c R (P + g)) = gauss (scl c R P) := by rw [scl_add]; exact gauss_add_eq_of_lt hg
    rw [h0, scl, zero_comp, gauss_zero] at h1
    exact gauss_ne_zero hsP h1.symm
  rw [Ncl_eq c hR hPg, Ncl_eq c hR hP, Nop_eq c hR hPg, Nop_eq c hR hP]
  exact h

theorem v_eval_eq_gauss_scl (c : K) {R : K} (hR : R ≠ 0) (P : K[X]) {w : K} (hw : v (w - c) = v R)
    (hgen : ∀ β ∈ (scl c R P).roots, v β ≤ 1 → 1 ≤ v (hat c R w - β)) :
    v (P.eval w) = gauss (scl c R P) := by
  rw [← eval_scl_hat c hR P w]
  refine v_eval_eq_gauss _ ?_ hgen
  rw [show (w - c) / R = hat c R w from rfl, v_hat_le_one_iff c hR, hw]

end SclAlgClosed

theorem eq_one_of_prod_eq_one {s : Multiset Γ₀} (hle : ∀ x ∈ s, x ≤ 1) (hprod : s.prod = 1) :
    ∀ x ∈ s, x = 1 := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    intro x hx
    rw [Multiset.prod_cons] at hprod
    have ha : a ≤ 1 := hle a (Multiset.mem_cons_self a s)
    have hs : s.prod ≤ 1 := by
      have := Multiset.prod_map_le_prod_map (s := s) id (fun _ => (1 : Γ₀))
        fun y hy => hle y (Multiset.mem_cons_of_mem hy)
      simpa using this
    have ha1 : a = 1 := by
      by_contra hne
      have hlt : a < 1 := lt_of_le_of_ne ha hne
      have : a * s.prod < 1 := mul_lt_one_of_lt_of_le hlt hs
      exact this.ne hprod
    rw [ha1, one_mul] at hprod
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · exact ha1
    · exact ih (fun y hy => hle y (Multiset.mem_cons_of_mem hy)) hprod x hx

theorem exists_generic_unit [IsAlgClosed K] (T : Multiset K) (hT : ∀ b ∈ T, Valued.v b ≤ 1) :
    ∃ u : K, Valued.v u = 1 ∧ ∀ b ∈ T, Valued.v (u - b) = 1 := by
  set T' : Multiset K := 0 ::ₘ T with hT'
  have hT'le : ∀ b ∈ T', Valued.v b ≤ 1 := fun b hb => by
    rcases Multiset.mem_cons.1 hb with rfl | hb
    · simp
    · exact hT b hb
  set F : K[X] := (T'.map fun b => X - C b).prod + 1 with hF
  have hmonic : (T'.map fun b => X - C b).prod.Monic := by
    refine monic_multiset_prod_of_monic _ _ fun b _ => monic_X_sub_C b
  have hdegprod : (T'.map fun b => X - C b).prod.natDegree = Multiset.card T' := by
    rw [natDegree_multiset_prod_of_monic]
    · simp
    · intro f hf
      obtain ⟨b, -, rfl⟩ := Multiset.mem_map.1 hf
      exact monic_X_sub_C b
  have hcard : 0 < Multiset.card T' := by rw [hT', Multiset.card_cons]; omega
  have hFdeg : F.degree ≠ 0 := by
    have h1 : F.natDegree = Multiset.card T' := by
      rw [hF, natDegree_add_eq_left_of_degree_lt, hdegprod]
      rw [degree_one, degree_eq_natDegree hmonic.ne_zero, hdegprod]
      exact_mod_cast hcard
    intro h0
    have := natDegree_eq_zero_iff_degree_le_zero.2 h0.le
    omega
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_root F hFdeg
  have hprod : (T'.map fun b => u - b).prod = -1 := by
    have h := hu
    rw [IsRoot, hF, eval_add, eval_one, eval_multiset_prod, Multiset.map_map, add_eq_zero_iff_eq_neg] at h
    convert h using 2 <;> try rfl
    refine Multiset.map_congr rfl fun b _ => ?_
    simp
  have hvprod : (T'.map fun b => Valued.v (u - b)).prod = 1 := by
    have := congrArg Valued.v hprod
    rw [Valuation.map_neg, Valuation.map_one, map_multiset_prod, Multiset.map_map] at this
    exact this
  have hule : Valued.v u ≤ 1 := by
    by_contra hgt
    push Not at hgt
    have hfac : ∀ b ∈ T', Valued.v (u - b) = Valued.v u := fun b hb =>
      Valuation.map_sub_eq_of_lt_left _ ((hT'le b hb).trans_lt hgt)
    have : (T'.map fun b => Valued.v (u - b)).prod = (T'.map fun _ => Valued.v u).prod :=
      congrArg Multiset.prod (Multiset.map_congr rfl hfac)
    rw [hvprod, Multiset.map_const', Multiset.prod_replicate] at this
    have h1 : (1 : Γ₀) < Valued.v u ^ Multiset.card T' := one_lt_pow₀ hgt hcard.ne'
    exact h1.ne this
  have hfacle : ∀ x ∈ T'.map (fun b => Valued.v (u - b)), x ≤ 1 := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 hx
    exact (Valuation.map_sub _ _ _).trans (max_le hule (hT'le b hb))
  have hall := eq_one_of_prod_eq_one hfacle hvprod
  have hone : ∀ b ∈ T', Valued.v (u - b) = 1 := fun b hb => hall _ (Multiset.mem_map_of_mem _ hb)
  refine ⟨u, ?_, fun b hb => hone b (Multiset.mem_cons_of_mem hb)⟩
  have := hone 0 (Multiset.mem_cons_self 0 T)
  rwa [sub_zero] at this

theorem exists_generic_unit' [IsAlgClosed K] (T : Multiset K) :
    ∃ u : K, Valued.v u = 1 ∧ ∀ b ∈ T, 1 ≤ Valued.v (u - b) := by
  classical
  obtain ⟨u, hu1, hu⟩ := exists_generic_unit (T.filter fun b => Valued.v b ≤ 1)
    (fun b hb => (Multiset.mem_filter.1 hb).2)
  refine ⟨u, hu1, fun b hb => ?_⟩
  rcases le_or_gt (Valued.v b) 1 with h | h
  · exact (hu b (Multiset.mem_filter.2 ⟨hb, h⟩)).ge
  · rw [Valuation.map_sub_eq_of_lt_right _ (hu1.trans_lt h)]; exact h.le

theorem exists_generic_point [IsAlgClosed K] (c : K) {R : K} (hR : R ≠ 0) (A : Multiset K) (B : Multiset K) :
    ∃ w : K, v (w - c) = v R ∧ (∀ a ∈ A, v R ≤ v (w - a)) ∧ ∀ β ∈ B, 1 ≤ v (hat c R w - β) := by
  obtain ⟨u, hu1, hu⟩ := exists_generic_unit' (K := K) (A.map (hat c R) + B)
  have hvR : 0 < v R := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hR)
  refine ⟨c + R * u, ?_, fun a ha => ?_, fun β hβ => ?_⟩
  · rw [show c + R * u - c = R * u by ring, map_mul, hu1, mul_one]
  · have h1 := hu _ (Multiset.mem_add.2 (Or.inl (Multiset.mem_map.2 ⟨a, ha, rfl⟩)))
    have : c + R * u - a = R * (u - hat c R a) := by rw [hat]; field_simp; ring
    rw [this, map_mul]
    calc v R = v R * 1 := (mul_one _).symm
      _ ≤ v R * v (u - hat c R a) := mul_le_mul' le_rfl h1
  · have : hat c R (c + R * u) = u := by rw [hat]; field_simp; ring
    rw [this]
    exact hu β (Multiset.mem_add.2 (Or.inr hβ))

section Book

variable (c R : K) (H : Finset K) (ρ : K → K)

def inD (h α : K) : Prop := Valued.v (α - h) ≤ Valued.v (ρ h)

def inB (α : K) : Prop := Valued.v (α - c) < Valued.v R

def inU (α : K) : Prop := Valued.v (α - c) < Valued.v R ∧ ∀ h ∈ H, Valued.v (ρ h) < Valued.v (α - h)

scoped instance (h α : K) : Decidable (inD ρ h α) := by unfold inD; infer_instance
scoped instance (α : K) : Decidable (inB c R α) := by unfold inB; infer_instance
scoped instance (α : K) : Decidable (inU c R H ρ α) := by unfold inU; infer_instance

variable {c R H ρ}

theorem inB_of_inD (hHc : ∀ h ∈ H, v (h - c) < v R) (hHR : ∀ h ∈ H, v (ρ h) < v R)
    {h : K} (hh : h ∈ H) {α : K} (hα : inD ρ h α) : inB c R α := by
  unfold inD at hα; unfold inB
  have : α - c = (α - h) + (h - c) := by ring
  rw [this]
  exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (hα.trans_lt (hHR h hh)) (hHc h hh))

theorem eq_of_inD_of_inD (hdisj : ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → v (ρ h) < v (h - h'))
    {h h' : K} (hh : h ∈ H) (hh' : h' ∈ H) {α : K} (hα : inD ρ h α) (hα' : inD ρ h' α) : h = h' := by
  by_contra hne
  unfold inD at hα hα'
  have h1 := hdisj h hh h' hh' hne
  have h2 := hdisj h' hh' h hh (Ne.symm hne)
  have : h - h' = (α - h') - (α - h) := by ring
  have h3 : v (h - h') ≤ max (v (α - h')) (v (α - h)) := by rw [this]; exact Valuation.map_sub _ _ _
  rw [Valuation.map_sub_swap] at h2
  rcases le_max_iff.1 h3 with h4 | h4
  · exact (lt_irrefl _) ((h2.trans_le h4).trans_le hα')
  · exact (lt_irrefl _) ((h1.trans_le h4).trans_le hα)

theorem indicator_identity (hHc : ∀ h ∈ H, v (h - c) < v R) (hHR : ∀ h ∈ H, v (ρ h) < v R)
    (hdisj : ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → v (ρ h) < v (h - h')) (α : K) :
    (if inB c R α then 1 else 0 : ℕ) = (if inU c R H ρ α then 1 else 0) + ∑ h ∈ H, (if inD ρ h α then 1 else 0) := by
  classical
  by_cases hB : inB c R α
  · rw [if_pos hB]
    by_cases hex : ∃ h ∈ H, inD ρ h α
    · obtain ⟨h₀, hh₀, hD⟩ := hex
      have hU : ¬ inU c R H ρ α := fun hU => (not_lt_of_ge hD) (hU.2 h₀ hh₀)
      rw [if_neg hU, zero_add]
      have hfilter : H.filter (fun h => inD ρ h α) = {h₀} := by
        ext h
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hh, hDh⟩; exact eq_of_inD_of_inD hdisj hh hh₀ hDh hD
        · rintro rfl; exact ⟨hh₀, hD⟩
      rw [← Finset.sum_filter_add_sum_filter_not H (fun h => inD ρ h α), hfilter, Finset.sum_singleton, if_pos hD,
        Finset.sum_eq_zero fun h hh => if_neg (Finset.mem_filter.1 hh).2, add_zero]
    · push Not at hex
      have hU : inU c R H ρ α := ⟨hB, fun h hh => lt_of_not_ge (hex h hh)⟩
      rw [if_pos hU, Finset.sum_eq_zero fun h hh => if_neg (hex h hh), add_zero]
  · rw [if_neg hB]
    have hU : ¬ inU c R H ρ α := fun hU => hB hU.1
    rw [if_neg hU, zero_add, eq_comm]
    exact Finset.sum_eq_zero fun h hh => if_neg fun hD => hB (inB_of_inD hHc hHR hh hD)

theorem countP_inB (hHc : ∀ h ∈ H, v (h - c) < v R) (hHR : ∀ h ∈ H, v (ρ h) < v R)
    (hdisj : ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → v (ρ h) < v (h - h')) (s : Multiset K) :
    s.countP (inB c R) = s.countP (inU c R H ρ) + ∑ h ∈ H, s.countP (inD ρ h) := by
  induction s using Multiset.induction with
  | empty => simp
  | cons α s ih =>
    simp only [Multiset.countP_cons]
    rw [ih, Finset.sum_add_distrib, indicator_identity hHc hHR hdisj α]
    ring

end Book

theorem Ncl_mul (c R : K) {P Q : K[X]} (h : P * Q ≠ 0) : Ncl c R (P * Q) = Ncl c R P + Ncl c R Q := by
  rw [Ncl, roots_mul h, Multiset.countP_add]; rfl

theorem Nop_mul (c R : K) {P Q : K[X]} (h : P * Q ≠ 0) : Nop c R (P * Q) = Nop c R P + Nop c R Q := by
  rw [Nop, roots_mul h, Multiset.countP_add]; rfl

section Main

theorem unif_eps {α : Type} {F : ℕ → α → K} {φ : α → K} (h : TendstoUniformly F φ atTop) :
    ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z, v (F k z - φ z) < v e := fun e he => by
  rw [tendstoUniformly_iff_vRestrict] at h
  have hwe : vRestrict K e ≠ 0 := by rwa [ne_eq, map_eq_zero]
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h (Units.mk0 _ hwe))
  exact ⟨N, fun k hk z => (v_lt_iff_vRestrict_lt K _ _).2 (hN k hk z)⟩

theorem exists_lt_finset {x : K} (hx0 : x ≠ 0) (hx1 : v x < 1) (A : Finset K) (hA : A.Nonempty)
    (hA0 : ∀ a ∈ A, a ≠ 0) : ∃ e : K, e ≠ 0 ∧ ∀ a ∈ A, v e < v a := by
  obtain ⟨m, hm, hmin⟩ := A.exists_min_image (fun a => v a) hA
  refine ⟨x * m, mul_ne_zero hx0 (hA0 m hm), fun a ha => ?_⟩
  rw [map_mul]
  calc v x * v m < 1 * v m := mul_lt_mul_of_pos_right hx1 ((Valuation.pos_iff _).2 (hA0 m hm))
    _ = v m := one_mul _
    _ ≤ v a := hmin a ha

theorem exists_disc {S : Set K} {c R : K} {H : Finset K} {ρ : K → K} {x : K} (hx0 : x ≠ 0) (hx1 : v x < 1)
    (hR : R ≠ 0)
    (hU : ∀ z : K, v (z - c) < v R → (∀ h ∈ H, v (ρ h) < v (z - h)) → z ∈ S)
    {a : K} (ha : inU c R H ρ a) :
    ∃ r : K, r ≠ 0 ∧ ∀ w : K, v (w - a) ≤ v r → w ∈ S := by
  classical
  have hne : (insert R (H.image fun h => a - h)).Nonempty := ⟨R, Finset.mem_insert_self _ _⟩
  have h0 : ∀ y ∈ insert R (H.image fun h => a - h), y ≠ 0 := by
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hR
    · obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hy
      intro h0
      have := ha.2 h hh
      rw [h0, map_zero] at this
      exact not_lt_of_ge zero_le' this
  obtain ⟨r, hr0, hr⟩ := exists_lt_finset hx0 hx1 _ hne h0
  refine ⟨r, hr0, fun w hw => hU w ?_ fun h hh => ?_⟩
  · have h1 : v (w - a) < v R := hw.trans_lt (hr R (Finset.mem_insert_self _ _))
    have : w - c = (w - a) + (a - c) := by ring
    rw [this]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt h1 ha.1)
  · have h1 : v (w - a) < v (a - h) :=
      hw.trans_lt (hr _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨h, hh, rfl⟩)))
    have : w - h = (w - a) + (a - h) := by ring
    rw [this, Valuation.map_add_eq_of_lt_right _ h1]
    exact ha.2 h hh

variable [CompleteSpace K] [IsAlgClosed K]

theorem peel {S : Set K} (c R : K) (hR : R ≠ 0) (H : Finset K) (ρ : K → K) {x : K} (hx0 : x ≠ 0) (hx1 : v x < 1)
    (hU : ∀ z : K, v (z - c) < v R → (∀ h ∈ H, v (ρ h) < v (z - h)) → z ∈ S)
    (F : Finset ↥S) :
    ∀ f : ↥S → K, f ∈ holOn K S → (∀ z ∈ F, inU c R H ρ (z : K)) → (∀ z ∈ F, f z = 0) →
      ∃ g : ↥S → K, g ∈ holOn K S ∧ ∀ z : ↥S, f z = (∏ ζ ∈ F, ((z : K) - (ζ : K))) * g z := by
  classical
  induction F using Finset.induction with
  | empty => intro f hf _ _; exact ⟨f, hf, fun z => by simp⟩
  | insert a F haF ih =>
    intro f hf hUF h0F
    obtain ⟨ra, hra0, hraS⟩ := exists_disc hx0 hx1 hR hU (hUF a (Finset.mem_insert_self a F))
    obtain ⟨g₁, hg₁, hfg₁⟩ := CerednikDrinfeld.Omega.exists_mem_holOn_eq_sub_mul_of_apply_eq_zero K hf a
      (h0F a (Finset.mem_insert_self a F)) ra hra0 hraS
    have hg₁0 : ∀ z ∈ F, g₁ z = 0 := by
      intro z hz
      have hne : (z : K) - (a : K) ≠ 0 := by
        intro h0
        apply haF
        have : z = a := Subtype.ext (sub_eq_zero.1 h0)
        rwa [← this]
      have := hfg₁ z
      rw [h0F z (Finset.mem_insert_of_mem hz)] at this
      exact (mul_eq_zero.1 this.symm).resolve_left hne
    obtain ⟨g, hg, hg₁g⟩ := ih g₁ hg₁ (fun z hz => hUF z (Finset.mem_insert_of_mem hz)) hg₁0
    refine ⟨g, hg, fun z => ?_⟩
    rw [Finset.prod_insert haF, hfg₁ z, hg₁g z]; ring

theorem locked {S : Set K} {f : ↥S → K} (c' : K) {R' : K} (hR' : R' ≠ 0) (E' Z' : Finset K) {s' e : K}
    (hS' : ∀ z : K, v (z - c') = v R' → (∀ e ∈ E', v R' ≤ v (z - e)) → z ∈ S)
    (hfeq : ∀ z : ↥S, v ((z : K) - c') = v R' → (∀ e ∈ E', v R' ≤ v ((z : K) - e)) →
      (∀ ζ ∈ Z', v R' ≤ v ((z : K) - ζ)) → v (f z) = v s')
    (hes : v e < v s')
    (p q p' q' : K[X]) (hq : ∀ z : ↥S, q.eval (z : K) ≠ 0) (hq' : ∀ z : ↥S, q'.eval (z : K) ≠ 0)
    (hcl : ∀ z : ↥S, v ((z : K) - c') = v R' → (∀ e ∈ E', v R' ≤ v ((z : K) - e)) →
      v (p.eval (z : K) / q.eval (z : K) - f z) < v e)
    (hcl' : ∀ z : ↥S, v ((z : K) - c') = v R' → (∀ e ∈ E', v R' ≤ v ((z : K) - e)) →
      v (p'.eval (z : K) / q'.eval (z : K) - f z) < v e) :
    Ncl c' R' (p * q') = Ncl c' R' (p' * q) ∧ Nop c' R' (p * q') = Nop c' R' (p' * q) ∧ p ≠ 0 ∧ p' ≠ 0 := by
  classical
  set A : K[X] := p * q' with hA
  set B : K[X] := p' * q with hB
  set g₀ : K[X] := B - A with hg₀

  obtain ⟨w, hwc, hwEZ, hwgen⟩ := exists_generic_point c' hR' (E'.val + Z'.val)
    ((scl c' R' A).roots + (scl c' R' B).roots + (scl c' R' g₀).roots + (scl c' R' q).roots + (scl c' R' q').roots)
  have hwE : ∀ e ∈ E', v R' ≤ v (w - e) := fun e he => hwEZ e (Multiset.mem_add.2 (Or.inl (Finset.mem_def.mp he)))
  have hwZ : ∀ ζ ∈ Z', v R' ≤ v (w - ζ) := fun ζ hζ => hwEZ ζ (Multiset.mem_add.2 (Or.inr (Finset.mem_def.mp hζ)))
  have hwS : w ∈ S := hS' w hwc hwE
  set W : ↥S := ⟨w, hwS⟩ with hW
  have hfw : v (f W) = v s' := hfeq W hwc hwE hwZ
  have hs'0 : (0 : Γ₀) < v s' := lt_of_le_of_lt zero_le' hes

  have hr : v (p.eval w / q.eval w) = v s' := by
    have h1 := hcl W hwc hwE
    have : v (p.eval w / q.eval w - f W) < v (f W) := by rw [hfw]; exact h1.trans hes
    rw [← hfw]; exact Valuation.map_eq_of_sub_lt _ this
  have hr' : v (p'.eval w / q'.eval w) = v s' := by
    have h1 := hcl' W hwc hwE
    have : v (p'.eval w / q'.eval w - f W) < v (f W) := by rw [hfw]; exact h1.trans hes
    rw [← hfw]; exact Valuation.map_eq_of_sub_lt _ this
  have hp0 : p ≠ 0 := by
    intro h0; rw [h0, eval_zero, zero_div, map_zero] at hr; exact hs'0.ne hr
  have hp'0 : p' ≠ 0 := by
    intro h0; rw [h0, eval_zero, zero_div, map_zero] at hr'; exact hs'0.ne hr'
  have hqw : q.eval w ≠ 0 := hq W
  have hq'w : q'.eval w ≠ 0 := hq' W
  have hdiff : v (p.eval w / q.eval w - p'.eval w / q'.eval w) < v e := by
    have : p.eval w / q.eval w - p'.eval w / q'.eval w =
        (p.eval w / q.eval w - f W) - (p'.eval w / q'.eval w - f W) := by ring
    rw [this]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (hcl W hwc hwE) (hcl' W hwc hwE))

  have hAw : A.eval w = q.eval w * q'.eval w * (p.eval w / q.eval w) := by
    rw [hA, eval_mul]; field_simp
  have hg₀w : g₀.eval w = -(q.eval w * q'.eval w * (p.eval w / q.eval w - p'.eval w / q'.eval w)) := by
    rw [hg₀, hB, hA, eval_sub, eval_mul, eval_mul]; field_simp; ring
  have hqq : (0 : Γ₀) < v (q.eval w * q'.eval w) := (Valuation.pos_iff _).2 (mul_ne_zero hqw hq'w)
  have hlt : v (g₀.eval w) < v (A.eval w) := by
    rw [hg₀w, hAw, Valuation.map_neg, Valuation.map_mul _ (q.eval w * q'.eval w),
      Valuation.map_mul _ (q.eval w * q'.eval w), hr]
    exact mul_lt_mul_of_pos_left (hdiff.trans hes) hqq

  have hA0 : A ≠ 0 := mul_ne_zero hp0 fun h0 => hq'w (by rw [h0, eval_zero])
  have hgen : ∀ P ∈ [A, B, g₀, q, q'], ∀ β ∈ (scl c' R' P).roots, v β ≤ 1 → 1 ≤ v (hat c' R' w - β) := by
    intro P hP β hβ hβ1
    apply hwgen β
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hP
    rcases hP with rfl | rfl | rfl | rfl | rfl <;> simp [hβ]
  by_cases hg00 : g₀ = 0
  · have hBA : B = A := sub_eq_zero.1 hg00
    rw [hBA]
    exact ⟨rfl, rfl, hp0, hp'0⟩
  · have hGlt : gauss (scl c' R' g₀) < gauss (scl c' R' A) := by
      rw [← v_eval_eq_gauss_scl c' hR' A hwc (hgen A (by simp)), ← v_eval_eq_gauss_scl c' hR' g₀ hwc (hgen g₀ (by simp))]
      exact hlt
    obtain ⟨h1, h2⟩ := rouche_at c' hR' hA0 hGlt
    have hBeq : A + g₀ = B := by rw [hg₀]; ring
    rw [hBeq] at h1 h2
    exact ⟨h1.symm, h2.symm, hp0, hp'0⟩

theorem main {S : Set K} {f : ↥S → K} (hf : f ∈ holOn K S)
    (c R : K) (hR : R ≠ 0)
    (H : Finset K) (ρ : K → K) (hρ : ∀ h ∈ H, ρ h ≠ 0)
    (hHc : ∀ h ∈ H, v (h - c) < v R)
    (hdisj : ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → v (ρ h) < v (h - h'))
    (E : Finset K)
    (hU : ∀ z : K, v (z - c) < v R → (∀ h ∈ H, v (ρ h) < v (z - h)) → z ∈ S)
    (hout : ∀ z : K, v (z - c) = v R → (∀ e ∈ E, v R ≤ v (z - e)) → z ∈ S)
    (hin : ∀ h ∈ H, ∀ z : K, v (z - h) = v (ρ h) → (∀ e ∈ E, v (ρ h) ≤ v (z - e)) → z ∈ S)
    (hout₀ : ∃ z : ↥S, v ((z : K) - c) = v R ∧ (∀ e ∈ E, v R ≤ v ((z : K) - e)) ∧ f z ≠ 0)
    (hin₀ : ∀ h ∈ H, ∃ z : ↥S, v ((z : K) - h) = v (ρ h) ∧ (∀ e ∈ E, v (ρ h) ≤ v ((z : K) - e)) ∧ f z ≠ 0) :
    {z : ↥S | v ((z : K) - c) < v R ∧ (∀ h ∈ H, v (ρ h) < v ((z : K) - h)) ∧ f z = 0}.Finite := by
  classical
  have hvR : (0 : Γ₀) < v R := (Valuation.pos_iff _).2 hR

  by_cases hHR : ∀ h ∈ H, v (ρ h) < v R
  swap
  · push Not at hHR
    obtain ⟨h₀, hh₀, hR₀⟩ := hHR
    refine Set.Finite.subset Set.finite_empty ?_
    rintro z ⟨hzc, hzH, -⟩
    have h1 := hzH h₀ hh₀
    have : (z : K) - h₀ = ((z : K) - c) - (h₀ - c) := by ring
    have h2 : v ((z : K) - h₀) < v R := by
      rw [this]; exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hzc (hHc h₀ hh₀))
    exact absurd (hR₀.trans_lt (h1.trans h2)) (lt_irrefl _)

  by_cases hnt : ∃ x : K, x ≠ 0 ∧ v x < 1
  swap
  · push Not at hnt
    have hall : ∀ y : K, y ≠ 0 → v y = 1 := fun y hy =>
      le_antisymm (by
        have := hnt y⁻¹ (inv_ne_zero hy)
        rwa [map_inv₀, one_le_inv₀ ((Valuation.pos_iff _).2 hy)] at this) (hnt y hy)
    refine Set.Subsingleton.finite ?_
    rintro z ⟨hzc, -, -⟩ z' ⟨hz'c, -, -⟩
    have hz : (z : K) = c := by
      by_contra hne
      have := hall _ (sub_ne_zero.2 hne)
      rw [this, hall R hR] at hzc; exact lt_irrefl _ hzc
    have hz' : (z' : K) = c := by
      by_contra hne
      have := hall _ (sub_ne_zero.2 hne)
      rw [this, hall R hR] at hz'c; exact lt_irrefl _ hz'c
    exact Subtype.ext (hz.trans hz'.symm)
  obtain ⟨x, hx0, hx1⟩ := hnt

  obtain ⟨sO, hsO0, ZO, hZOle, hZOeq⟩ :=
    CerednikDrinfeld.Omega.exists_forall_v_apply_eq_on_circle_of_mem_holOn K hf c R hR E hout hout₀
  have hGMin : ∀ h ∈ H, ∃ s : K, s ≠ 0 ∧ ∃ Z : Finset K,
      (∀ z : ↥S, v ((z : K) - h) = v (ρ h) → (∀ e ∈ E, v (ρ h) ≤ v ((z : K) - e)) → v (f z) ≤ v s) ∧
      (∀ z : ↥S, v ((z : K) - h) = v (ρ h) → (∀ e ∈ E, v (ρ h) ≤ v ((z : K) - e)) →
        (∀ ζ ∈ Z, v (ρ h) ≤ v ((z : K) - ζ)) → v (f z) = v s) := fun h hh =>
    CerednikDrinfeld.Omega.exists_forall_v_apply_eq_on_circle_of_mem_holOn K hf h (ρ h) (hρ h hh) E (hin h hh) (hin₀ h hh)
  choose! sI hsI0 ZI hZIle hZIeq using hGMin

  obtain ⟨e, he0, he⟩ := exists_lt_finset hx0 hx1 (insert sO (H.image sI)) ⟨sO, Finset.mem_insert_self _ _⟩
    (fun a ha => by
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact hsO0
      · obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 ha; exact hsI0 h hh)
  have heO : v e < v sO := he sO (Finset.mem_insert_self _ _)
  have heI : ∀ h ∈ H, v e < v (sI h) := fun h hh =>
    he _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨h, hh, rfl⟩))

  have hf' := hf
  obtain ⟨r, hpf, -, hlim⟩ := hf'
  obtain ⟨N₁, hN₁⟩ := unif_eps hlim e he0
  set p : K[X] := (r N₁).num with hp
  set q : K[X] := (r N₁).den with hq
  have hqS : ∀ z : ↥S, q.eval (z : K) ≠ 0 := fun z => hpf N₁ z z.2
  have hclose : ∀ z : ↥S, v (p.eval (z : K) / q.eval (z : K) - f z) < v e := fun z => hN₁ N₁ le_rfl z

  set N : ℕ := p.roots.countP (inU c R H ρ) with hN
  by_contra hinf
  obtain ⟨F, hFsub, hFcard⟩ := Set.Infinite.exists_subset_card_eq hinf (N + 1)
  have hFmem : ∀ z ∈ F, v ((z : K) - c) < v R ∧ (∀ h ∈ H, v (ρ h) < v ((z : K) - h)) ∧ f z = 0 :=
    fun z hz => hFsub (Finset.mem_coe.2 hz)
  have hFU : ∀ z ∈ F, inU c R H ρ (z : K) := fun z hz => ⟨(hFmem z hz).1, (hFmem z hz).2.1⟩
  have hF0 : ∀ z ∈ F, f z = 0 := fun z hz => (hFmem z hz).2.2

  obtain ⟨g, hg, hfg⟩ := peel c R hR H ρ hx0 hx1 hU F f hf hFU hF0
  obtain ⟨qs, hqpf, -, hqlim⟩ := hg
  obtain ⟨N₂, hN₂⟩ := unif_eps hqlim (e / R ^ (N + 1)) (div_ne_zero he0 (pow_ne_zero _ hR))
  set n₂ : K[X] := (qs N₂).num with hn₂
  set d₂ : K[X] := (qs N₂).den with hd₂
  have hd₂S : ∀ z : ↥S, d₂.eval (z : K) ≠ 0 := fun z => hqpf N₂ z z.2
  set Pi : K[X] := ∏ ζ ∈ F, (X - C (ζ : K)) with hPi
  set ñ : K[X] := Pi * n₂ with hñ
  have hPiev : ∀ w : K, Pi.eval w = ∏ ζ ∈ F, (w - (ζ : K)) := fun w => by
    rw [hPi, eval_prod]; simp
  have hñev : ∀ z : ↥S, ñ.eval (z : K) / d₂.eval (z : K) - f z =
      (∏ ζ ∈ F, ((z : K) - (ζ : K))) * ((qs N₂).evalAt z - g z) := fun z => by
    rw [hñ, eval_mul, hPiev, hfg z, mul_sub, mul_div_assoc]; rfl
  have hclose' : ∀ z : ↥S, v (∏ ζ ∈ F, ((z : K) - (ζ : K))) ≤ v R ^ (N + 1) →
      v (ñ.eval (z : K) / d₂.eval (z : K) - f z) < v e := by
    intro z hz
    rw [hñev z, map_mul]
    have h1 := hN₂ N₂ le_rfl z
    calc v (∏ ζ ∈ F, ((z : K) - (ζ : K))) * v ((qs N₂).evalAt z - g z)
        < v R ^ (N + 1) * v (e / R ^ (N + 1)) :=
          mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hz h1 zero_le' (pow_pos hvR _)
      _ = v e := by rw [map_div₀, map_pow, mul_div_cancel₀ _ (pow_ne_zero _ hvR.ne')]

  have hprod_out : ∀ z : ↥S, v ((z : K) - c) = v R → v (∏ ζ ∈ F, ((z : K) - (ζ : K))) ≤ v R ^ (N + 1) := by
    intro z hz
    rw [map_prod, ← hFcard]
    refine Finset.prod_le_pow_card F _ _ fun ζ hζ => ?_
    have : (z : K) - ζ = ((z : K) - c) - ((ζ : K) - c) := by ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le hz.le (hFU ζ hζ).1.le)
  have hprod_in : ∀ h ∈ H, ∀ z : ↥S, v ((z : K) - h) = v (ρ h) →
      v (∏ ζ ∈ F, ((z : K) - (ζ : K))) ≤ v R ^ (N + 1) := by
    intro h hh z hz
    rw [map_prod, ← hFcard]
    refine Finset.prod_le_pow_card F _ _ fun ζ hζ => ?_
    have h1 : v ((z : K) - h) < v ((ζ : K) - h) := by rw [hz]; exact (hFU ζ hζ).2 h hh
    have : (z : K) - ζ = ((z : K) - h) - ((ζ : K) - h) := by ring
    rw [this, Valuation.map_sub_eq_of_lt_right _ h1]
    have : (ζ : K) - h = ((ζ : K) - c) - (h - c) := by ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le (hFU ζ hζ).1.le (hHc h hh).le)

  obtain ⟨-, hNout, hp0, hñ0⟩ := locked (f := f) c hR E ZO hout hZOeq heO p q ñ d₂ hqS hd₂S
    (fun z _ _ => hclose z) (fun z hz _ => hclose' z (hprod_out z hz))
  have hNin : ∀ h ∈ H, Ncl h (ρ h) (p * d₂) = Ncl h (ρ h) (ñ * q) := fun h hh =>
    (locked (f := f) h (hρ h hh) E (ZI h) (hin h hh) (hZIeq h hh) (heI h hh) p q ñ d₂ hqS hd₂S
      (fun z _ _ => hclose z) (fun z hz _ => hclose' z (hprod_in h hh z hz))).1

  have hq0 : q ≠ 0 := by
    obtain ⟨z₀, -⟩ := hout₀; intro h0; exact hqS z₀ (by rw [h0, eval_zero])
  have hd₂0 : d₂ ≠ 0 := by
    obtain ⟨z₀, -⟩ := hout₀; intro h0; exact hd₂S z₀ (by rw [h0, eval_zero])
  have hn₂0 : n₂ ≠ 0 := fun h0 => hñ0 (by rw [hñ, h0, mul_zero])
  have hPi0 : Pi ≠ 0 := fun h0 => hñ0 (by rw [hñ, h0, zero_mul])
  have hNopB : ∀ P : K[X], Nop c R P = P.roots.countP (inB c R) := fun P =>
    Multiset.countP_congr rfl fun x _ => rfl
  have hNclD : ∀ (h : K) (P : K[X]), Ncl h (ρ h) P = P.roots.countP (inD ρ h) := fun h P =>
    Multiset.countP_congr rfl fun x _ => rfl
  have hsplit : ∀ P : K[X], Nop c R P = P.roots.countP (inU c R H ρ) + ∑ h ∈ H, Ncl h (ρ h) P := by
    intro P
    rw [hNopB, countP_inB hHc hHR hdisj P.roots]
    simp only [hNclD]

  have hUq : q.roots.countP (inU c R H ρ) = 0 := by
    refine Multiset.countP_eq_zero.2 fun α hα hUα => ?_
    have hαS : α ∈ S := hU α hUα.1 hUα.2
    exact hqS ⟨α, hαS⟩ ((mem_roots hq0).1 hα)
  have hUd₂ : d₂.roots.countP (inU c R H ρ) = 0 := by
    refine Multiset.countP_eq_zero.2 fun α hα hUα => ?_
    have hαS : α ∈ S := hU α hUα.1 hUα.2
    exact hd₂S ⟨α, hαS⟩ ((mem_roots hd₂0).1 hα)

  have hPiroots : Pi.roots = F.val.map fun ζ : ↥S => (ζ : K) := by
    rw [hPi, roots_prod _ _ (by rw [← hPi]; exact hPi0)]
    simp only [roots_X_sub_C]
    rw [Multiset.bind_singleton]
  have hUPi : Pi.roots.countP (inU c R H ρ) = N + 1 := by
    rw [hPiroots, ← hFcard]
    have : (F.val.map fun ζ : ↥S => (ζ : K)).countP (inU c R H ρ) = Multiset.card (F.val.map fun ζ : ↥S => (ζ : K)) :=
      Multiset.countP_eq_card.2 fun α hα => by
        obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.1 hα
        exact hFU ζ hζ
    rw [this, Multiset.card_map]; rfl
  have hUñ : ñ.roots.countP (inU c R H ρ) = N + 1 + n₂.roots.countP (inU c R H ρ) := by
    rw [hñ, roots_mul (mul_ne_zero hPi0 hn₂0), Multiset.countP_add, hUPi]

  have hpd : p * d₂ ≠ 0 := mul_ne_zero hp0 hd₂0
  have hñq : ñ * q ≠ 0 := mul_ne_zero hñ0 hq0
  rw [Nop_mul c R hpd, Nop_mul c R hñq, hsplit p, hsplit d₂, hsplit ñ, hsplit q, hUq, hUd₂, hUñ] at hNout
  have hsum : ∑ h ∈ H, Ncl h (ρ h) p + ∑ h ∈ H, Ncl h (ρ h) d₂ = ∑ h ∈ H, Ncl h (ρ h) ñ + ∑ h ∈ H, Ncl h (ρ h) q := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [← Ncl_mul h (ρ h) hpd, ← Ncl_mul h (ρ h) hñq]
    exact hNin h hh
  omega

end Main

end P2mKcRimCount
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_openDisc_sdiff_of_mem_holOn.P2mKcRimCount"

theorem solution
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    [CompleteSpace K] [IsAlgClosed K]
    {S : Set K} {f : ↥S → K} (hf : f ∈ holOn K S)
    (c R : K) (hR : R ≠ 0)
    (H : Finset K) (ρ : K → K) (hρ : ∀ h ∈ H, ρ h ≠ 0)
    (hHc : ∀ h ∈ H, Valued.v (h - c) < Valued.v R)
    (hdisj : ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → Valued.v (ρ h) < Valued.v (h - h'))
    (E : Finset K)
    (hU : ∀ z : K, Valued.v (z - c) < Valued.v R → (∀ h ∈ H, Valued.v (ρ h) < Valued.v (z - h)) → z ∈ S)
    (hout : ∀ z : K, Valued.v (z - c) = Valued.v R → (∀ e ∈ E, Valued.v R ≤ Valued.v (z - e)) → z ∈ S)
    (hin : ∀ h ∈ H, ∀ z : K, Valued.v (z - h) = Valued.v (ρ h) →
      (∀ e ∈ E, Valued.v (ρ h) ≤ Valued.v (z - e)) → z ∈ S)
    (hout₀ : ∃ z : ↥S, Valued.v ((z : K) - c) = Valued.v R ∧
      (∀ e ∈ E, Valued.v R ≤ Valued.v ((z : K) - e)) ∧ f z ≠ 0)
    (hin₀ : ∀ h ∈ H, ∃ z : ↥S, Valued.v ((z : K) - h) = Valued.v (ρ h) ∧
      (∀ e ∈ E, Valued.v (ρ h) ≤ Valued.v ((z : K) - e)) ∧ f z ≠ 0) :
    {z : ↥S | Valued.v ((z : K) - c) < Valued.v R ∧
      (∀ h ∈ H, Valued.v (ρ h) < Valued.v ((z : K) - h)) ∧ f z = 0}.Finite :=
  P2mKcRimCount.main hf c R hR H ρ hρ hHc hdisj E hU hout hin hout₀ hin₀

end
end S_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_openDisc_sdiff_of_mem_holOn
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_openDisc_sdiff_of_mem_holOn (solution)
