-- Prove2me | solution 1 for CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_disc_of_mem_holOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/58f325ca-b4ed-5044-b925-b4cbdee86f4b

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_CerednikDrinfeld_Omega_RatPair_identityPrinciple_disc
import Theorems.Thm_CerednikDrinfeld_Omega_gaussNorm_add_eq_max_of_separated_poles
import Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_of_v_sub_lt_of_mem_holOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_disc_of_mem_holOn

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial CerednikDrinfeld.Omega

namespace IdAnn

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

end IdAnn

namespace IdAnn

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

def aff (c π : K) (r : RatPair K) : RatPair K := ⟨r.num.comp (C π * X + C c), r.den.comp (C π * X + C c)⟩

theorem aff_den_eval (c π : K) (r : RatPair K) (y : K) : (aff c π r).den.eval y = r.den.eval (π * y + c) := by
  simp [aff, eval_comp]

theorem aff_num_eval (c π : K) (r : RatPair K) (y : K) : (aff c π r).num.eval y = r.num.eval (π * y + c) := by
  simp [aff, eval_comp]

theorem aff_evalAt (c π : K) (r : RatPair K) (y : K) : (aff c π r).evalAt y = r.evalAt (π * y + c) := by
  rw [RatPair.evalAt, RatPair.evalAt, aff_den_eval, aff_num_eval]

section AlgClosed

variable [IsAlgClosed K]

theorem natDegree_eq_card_roots' (Q : K[X]) : Q.natDegree = Multiset.card Q.roots :=
  (IsAlgClosed.splits Q).natDegree_eq_card_roots

theorem gauss_eq_lc_of_roots (Q : K[X]) (h : ∀ α ∈ Q.roots, v α ≤ 1) : gauss Q = v Q.leadingCoeff := by
  rw [gauss_eq_prod_roots]
  have : (Q.roots.map fun α => max 1 (v α)) = Q.roots.map fun _ => (1 : Γ₀) :=
    Multiset.map_congr rfl fun α hα => max_eq_left (h α hα)
  rw [this, Multiset.map_const', Multiset.prod_replicate, one_pow, mul_one]

theorem orth_outer (PA QA PB QB : K[X]) (hQA : QA ≠ 0) (hQB : QB ≠ 0) (hdeg : PA.degree < QA.degree)
    (hA : ∀ α ∈ QA.roots, v α < 1) (hB : ∀ β ∈ QB.roots, 1 ≤ v β) :
    gauss (PA * QB + PB * QA) = max (gauss (PA * QB)) (gauss (PB * QA)) :=
  CerednikDrinfeld.Omega.gaussNorm_add_eq_max_of_separated_poles K PA QA PB QB hQA hQB hdeg (Or.inl ⟨hA, hB⟩)

theorem orth_inner (PA QA PB QB : K[X]) (hQA : QA ≠ 0) (hQB : QB ≠ 0) (hdeg : PA.degree < QA.degree)
    (hA : ∀ α ∈ QA.roots, v α ≤ 1) (hB : ∀ β ∈ QB.roots, 1 < v β) :
    gauss (PA * QB + PB * QA) = max (gauss (PA * QB)) (gauss (PB * QA)) :=
  CerednikDrinfeld.Omega.gaussNorm_add_eq_max_of_separated_poles K PA QA PB QB hQA hQB hdeg (Or.inr ⟨hA, hB⟩)

theorem L0 (S : Set K) (r : ℕ → RatPair K) (hpf : ∀ k, (r k).IsPoleFreeOn S)
    (Z : Finset K) (hZ : ∀ ζ ∈ Z, 1 ≤ v ζ)
    (hS : ∀ y : K, v y ≤ 1 → (∀ ζ ∈ Z, 1 ≤ v (y - ζ)) → y ∈ S)
    (hC : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ y ∈ S, v ((r k).evalAt y - (r j).evalAt y) < v e)
    (δ : K) (hδ : δ ≠ 0)
    (h0 : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y ∈ S, v y ≤ v δ → v ((r k).evalAt y) < v e) :
    ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y ∈ S, v y ≤ 1 → (∀ ζ ∈ Z, 1 ≤ v (y - ζ)) →
      v ((r k).evalAt y) < v e := by
  have h := CerednikDrinfeld.Omega.RatPair.identityPrinciple_disc K S r hpf 0 1 one_ne_zero Z
    (fun ζ hζ => by rw [map_one, zero_sub, Valuation.map_neg]; exact hZ ζ hζ)
    (fun y hy hyZ => hS y (by rw [sub_zero, map_one] at hy; exact hy)
      (fun ζ hζ => by have := hyZ ζ hζ; rwa [map_one] at this))
    hC δ hδ (fun e he => by
      obtain ⟨N, hN⟩ := h0 e he
      exact ⟨N, fun k hk y hy hyδ => hN k hk y hy (by rw [sub_zero] at hyδ; exact hyδ)⟩)
  intro e he
  obtain ⟨N, hN⟩ := h e he
  exact ⟨N, fun k hk y _ hy hyZ => hN k hk y (by rw [sub_zero, map_one]; exact hy)
    (fun ζ hζ => by rw [map_one]; exact hyZ ζ hζ)⟩

end AlgClosed

end IdAnn

namespace IdAnn

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

open Classical in
/-!                                                                                             -/

section Split

variable [IsAlgClosed K] (σ : Γ₀)

open scoped Classical

def inRoots (Q : K[X]) : Multiset K := Q.roots.filter fun α => v α ≤ σ

def outRoots (Q : K[X]) : Multiset K := Q.roots.filter fun α => ¬ v α ≤ σ

def Qin (Q : K[X]) : K[X] := ((inRoots σ Q).map fun α => X - C α).prod

def Qout (Q : K[X]) : K[X] := C Q.leadingCoeff * ((outRoots σ Q).map fun α => X - C α).prod

omit [IsAlgClosed K] in
theorem Qin_monic (Q : K[X]) : (Qin σ Q).Monic := monic_multiset_prod_of_monic _ _ fun α _ => monic_X_sub_C α

omit [IsAlgClosed K] in
theorem Qin_ne_zero (Q : K[X]) : Qin σ Q ≠ 0 := (Qin_monic σ Q).ne_zero

theorem Qin_mul_Qout (Q : K[X]) : Qin σ Q * Qout σ Q = Q := by
  rw [Qin, Qout, mul_left_comm, ← Multiset.prod_add, ← Multiset.map_add, inRoots, outRoots, Multiset.filter_add_not]
  exact (eq_C_mul_prod Q).symm

theorem Qout_ne_zero {Q : K[X]} (hQ : Q ≠ 0) : Qout σ Q ≠ 0 := fun h => hQ (by rw [← Qin_mul_Qout σ Q, h, mul_zero])

omit [IsAlgClosed K] in
theorem roots_Qin (Q : K[X]) : (Qin σ Q).roots = inRoots σ Q := roots_multiset_prod_X_sub_C _

omit [IsAlgClosed K] in
theorem mem_roots_Qin {Q : K[X]} {α : K} : α ∈ (Qin σ Q).roots ↔ α ∈ Q.roots ∧ v α ≤ σ := by
  rw [roots_Qin, inRoots, Multiset.mem_filter]

omit [IsAlgClosed K] in
theorem roots_Qout {Q : K[X]} (hQ : Q ≠ 0) : (Qout σ Q).roots = outRoots σ Q := by
  rw [Qout, roots_C_mul _ (leadingCoeff_ne_zero.2 hQ), roots_multiset_prod_X_sub_C]

omit [IsAlgClosed K] in
theorem mem_roots_Qout {Q : K[X]} (hQ : Q ≠ 0) {α : K} : α ∈ (Qout σ Q).roots ↔ α ∈ Q.roots ∧ σ < v α := by
  rw [roots_Qout σ hQ, outRoots, Multiset.mem_filter, not_le]

omit [IsAlgClosed K] in
theorem natDegree_Qin (Q : K[X]) : (Qin σ Q).natDegree = Multiset.card (inRoots σ Q) := by
  rw [Qin, natDegree_multiset_prod_X_sub_C_eq_card]

theorem isCoprime_Qin_Qout (Q : K[X]) : IsCoprime (Qin σ Q) (Qout σ Q) := by
  rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed K K]
  intro a
  simp only [coe_aeval_eq_eval]
  by_cases hQ : Q = 0
  · left
    have : inRoots σ Q = 0 := by rw [inRoots, hQ, roots_zero, Multiset.filter_zero]
    rw [Qin, this, Multiset.map_zero, Multiset.prod_zero, eval_one]; exact one_ne_zero
  by_cases ha : v a ≤ σ
  · right
    intro h
    have hmem : a ∈ (Qout σ Q).roots := (mem_roots (Qout_ne_zero σ hQ)).2 h
    exact (not_le.2 ((mem_roots_Qout σ hQ).1 hmem).2) ha
  · left
    intro h
    have hmem : a ∈ (Qin σ Q).roots := (mem_roots (Qin_ne_zero σ Q)).2 h
    exact ha ((mem_roots_Qin σ).1 hmem).2

def bezA (Q : K[X]) : K[X] := Classical.choose (isCoprime_Qin_Qout σ Q)

def bezB (Q : K[X]) : K[X] := Classical.choose (Classical.choose_spec (isCoprime_Qin_Qout σ Q))

theorem bez_spec (Q : K[X]) : bezA σ Q * Qin σ Q + bezB σ Q * Qout σ Q = 1 :=
  Classical.choose_spec (Classical.choose_spec (isCoprime_Qin_Qout σ Q))

def inNum (P Q : K[X]) : K[X] := (P * bezB σ Q) %ₘ Qin σ Q

def outNum (P Q : K[X]) : K[X] := (P * bezB σ Q) /ₘ Qin σ Q * Qout σ Q + P * bezA σ Q

theorem split_eq (P Q : K[X]) : inNum σ P Q * Qout σ Q + outNum σ P Q * Qin σ Q = P := by
  have h1 := modByMonic_add_div (P * bezB σ Q) (Qin σ Q)
  have h2 := bez_spec σ Q
  rw [outNum, add_mul, inNum]
  calc (P * bezB σ Q) %ₘ Qin σ Q * Qout σ Q + ((P * bezB σ Q) /ₘ Qin σ Q * Qout σ Q * Qin σ Q + P * bezA σ Q * Qin σ Q)
        = ((P * bezB σ Q) %ₘ Qin σ Q + Qin σ Q * ((P * bezB σ Q) /ₘ Qin σ Q)) * Qout σ Q + P * bezA σ Q * Qin σ Q := by
          ring
    _ = P * (bezA σ Q * Qin σ Q + bezB σ Q * Qout σ Q) := by rw [h1]; ring
    _ = P := by rw [h2, mul_one]

theorem degree_inNum_lt (P Q : K[X]) : (inNum σ P Q).degree < (Qin σ Q).degree :=
  degree_modByMonic_lt _ (Qin_monic σ Q)

theorem natDegree_inNum_le (P Q : K[X]) : (inNum σ P Q).natDegree ≤ (Qin σ Q).natDegree := by
  by_cases h : inNum σ P Q = 0
  · rw [h, natDegree_zero]; exact Nat.zero_le _
  · exact (natDegree_lt_natDegree h (degree_inNum_lt σ P Q)).le

theorem eval_split (P Q : K[X]) {y : K} (hy : Q.eval y ≠ 0) :
    (Qin σ Q).eval y ≠ 0 ∧ (Qout σ Q).eval y ≠ 0 ∧
      P.eval y / Q.eval y = (inNum σ P Q).eval y / (Qin σ Q).eval y + (outNum σ P Q).eval y / (Qout σ Q).eval y := by
  have hQ : Q.eval y = (Qin σ Q).eval y * (Qout σ Q).eval y := by rw [← eval_mul, Qin_mul_Qout]
  rw [hQ] at hy
  have h1 : (Qin σ Q).eval y ≠ 0 := left_ne_zero_of_mul hy
  have h2 : (Qout σ Q).eval y ≠ 0 := right_ne_zero_of_mul hy
  refine ⟨h1, h2, ?_⟩
  rw [div_add_div _ _ h1 h2, hQ]
  congr 1
  conv_lhs => rw [← split_eq σ P Q]
  simp only [eval_add, eval_mul]
  ring

end Split

theorem v_eval_le_gauss_mul_pow (P : K[X]) {y : K} (hy : 1 ≤ v y) : v (P.eval y) ≤ gauss P * v y ^ P.natDegree := by
  rw [eval_eq_sum_range]
  refine Valuation.map_sum_le _ fun i hi => ?_
  rw [map_mul, map_pow]
  exact mul_le_mul' (v_coeff_le_gauss P i) (pow_le_pow_right₀ hy (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))

section AlgClosed

variable [IsAlgClosed K]

theorem v_div_le_out (P Q : K[X]) {y : K} (hy : v y ≤ 1)
    (hgen : ∀ α ∈ Q.roots, v α ≤ 1 → 1 ≤ v (y - α)) :
    v (P.eval y / Q.eval y) ≤ gauss P / gauss Q := by
  rw [map_div₀, v_eval_eq_gauss Q hy hgen]
  exact div_le_div_of_nonneg_right (v_eval_le_gauss P hy) zero_le'

theorem v_div_le_in (σ₀ : K) (hσ : σ₀ ≠ 0) (P Q : K[X]) (hQ : Q ≠ 0) (hdeg : P.natDegree ≤ Q.natDegree)
    (hroots : ∀ α ∈ Q.roots, v α ≤ v σ₀) {y : K} (hy : v σ₀ ≤ v y)
    (hgen : ∀ α ∈ Q.roots, v σ₀ ≤ v (y - α)) :
    v (P.eval y / Q.eval y) ≤ gauss (P.comp (C σ₀ * X)) / gauss (Q.comp (C σ₀ * X)) := by
  have hvσ : 0 < v σ₀ := (Valuation.pos_iff _).2 hσ
  set P' := P.comp (C σ₀ * X) with hP'
  set Q' := Q.comp (C σ₀ * X) with hQ'
  set y' := y / σ₀ with hy'
  have hyy : σ₀ * y' = y := by rw [hy']; field_simp
  have hvy' : 1 ≤ v y' := by rw [hy', map_div₀, le_div_iff₀ hvσ, one_mul]; exact hy
  have hvy'0 : 0 < v y' := zero_lt_one.trans_le hvy'
  have hPe : P.eval y = P'.eval y' := by rw [hP', eval_comp, eval_mul, eval_C, eval_X, hyy]
  have hQe : Q.eval y = Q'.eval y' := by rw [hQ', eval_comp, eval_mul, eval_C, eval_X, hyy]
  have hQ'ne : Q' ≠ 0 := by
    rw [hQ', Ne, comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_of_ne_zero hσ)]; exact hQ
  have hroots' : ∀ α' ∈ Q'.roots, v α' ≤ 1 := fun α' hα' => by
    have h : Q.eval (σ₀ * α') = 0 := by
      have := (mem_roots hQ'ne).1 hα'
      rwa [IsRoot.def, hQ', eval_comp, eval_mul, eval_C, eval_X] at this
    have hmem : σ₀ * α' ∈ Q.roots := (mem_roots hQ).2 h
    have := hroots _ hmem
    rw [map_mul] at this
    calc v α' = (v σ₀)⁻¹ * (v σ₀ * v α') := by rw [← mul_assoc, inv_mul_cancel₀ hvσ.ne', one_mul]
      _ ≤ (v σ₀)⁻¹ * v σ₀ := mul_le_mul' le_rfl this
      _ = 1 := inv_mul_cancel₀ hvσ.ne'
  have hgen' : ∀ α' ∈ Q'.roots, v y' ≤ v (y' - α') := fun α' hα' => by
    have h : Q.eval (σ₀ * α') = 0 := by
      have := (mem_roots hQ'ne).1 hα'
      rwa [IsRoot.def, hQ', eval_comp, eval_mul, eval_C, eval_X] at this
    have hmem : σ₀ * α' ∈ Q.roots := (mem_roots hQ).2 h
    rcases eq_or_lt_of_le hvy' with h1 | h1
    ·
      have := hgen _ hmem
      rw [← hyy, ← mul_sub, map_mul] at this
      rw [← h1]
      calc (1 : Γ₀) = (v σ₀)⁻¹ * v σ₀ := (inv_mul_cancel₀ hvσ.ne').symm
        _ ≤ (v σ₀)⁻¹ * (v σ₀ * v (y' - α')) := mul_le_mul' le_rfl this
        _ = v (y' - α') := by rw [← mul_assoc, inv_mul_cancel₀ hvσ.ne', one_mul]
    ·
      rw [Valuation.map_sub_eq_of_lt_left _ ((hroots' α' hα').trans_lt h1)]

  have hQlow : gauss Q' * v y' ^ Q'.natDegree ≤ v (Q'.eval y') := by
    conv_rhs => rw [eq_C_mul_prod Q']
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, map_mul, map_multiset_prod, Multiset.map_map,
      gauss_eq_lc_of_roots Q' hroots', natDegree_eq_card_roots' Q']
    refine mul_le_mul' le_rfl ?_
    have : v y' ^ Multiset.card Q'.roots = (Q'.roots.map fun _ => v y').prod := by
      rw [Multiset.map_const', Multiset.prod_replicate]
    rw [this]
    refine Multiset.prod_map_le_prod_map _ _ fun α' hα' => ?_
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
    exact hgen' α' hα'
  have hPup : v (P'.eval y') ≤ gauss P' * v y' ^ Q'.natDegree := by
    refine (v_eval_le_gauss_mul_pow P' hvy').trans (mul_le_mul' le_rfl (pow_le_pow_right₀ hvy' ?_))
    have h1 : P'.natDegree = P.natDegree := by rw [hP', natDegree_comp, natDegree_C_mul_X _ hσ, mul_one]
    have h2 : Q'.natDegree = Q.natDegree := by rw [hQ', natDegree_comp, natDegree_C_mul_X _ hσ, mul_one]
    rw [h1, h2]; exact hdeg
  have hQ'pos : 0 < v (Q'.eval y') := by
    rw [← hQe, Valuation.pos_iff]
    intro h
    have hmem : y ∈ Q.roots := (mem_roots hQ).2 h
    have := hgen y hmem
    rw [sub_self, map_zero] at this
    exact hvσ.not_ge this
  rw [hPe, hQe, map_div₀, div_le_div_iff₀ hQ'pos (gauss_pos hQ'ne)]
  calc v (P'.eval y') * gauss Q' ≤ gauss P' * v y' ^ Q'.natDegree * gauss Q' := mul_le_mul' hPup le_rfl
    _ = gauss P' * (gauss Q' * v y' ^ Q'.natDegree) := by rw [mul_assoc, mul_comm (gauss Q')]
    _ ≤ gauss P' * v (Q'.eval y') := mul_le_mul' le_rfl hQlow

end AlgClosed

def winv (σ₀ : K) (D : ℕ) (P Q : K[X]) : RatPair K :=
  ⟨RatPair.homog 0 σ₀ 1 0 D P, RatPair.homog 0 σ₀ 1 0 D Q⟩

theorem homog_eval_ne_zero {σ₀ : K} {D : ℕ} {P : K[X]} (hD : P.natDegree ≤ D) {w : K} (hw : w ≠ 0) :
    (RatPair.homog 0 σ₀ 1 0 D P).eval w = w ^ D * P.eval (σ₀ / w) := by
  rw [RatPair.eval_homog hD w (by rwa [one_mul, add_zero])]
  simp

theorem homog_eval_zero (σ₀ : K) (D : ℕ) (P : K[X]) : (RatPair.homog 0 σ₀ 1 0 D P).eval 0 = P.coeff D * σ₀ ^ D := by
  rw [RatPair.homog, eval_finsetSum, Finset.sum_eq_single D]
  · simp
  · intro i hi hiD
    have hlt : i < D := lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hiD
    simp [zero_pow (Nat.sub_ne_zero_of_lt hlt)]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self D)) h

theorem winv_evalAt {σ₀ : K} {D : ℕ} {P Q : K[X]} (hP : P.natDegree ≤ D) (hQ : Q.natDegree ≤ D) {w : K} (hw : w ≠ 0) :
    (winv σ₀ D P Q).evalAt w = P.eval (σ₀ / w) / Q.eval (σ₀ / w) := by
  rw [RatPair.evalAt, winv, homog_eval_ne_zero hP hw, homog_eval_ne_zero hQ hw,
    mul_div_mul_left _ _ (pow_ne_zero D hw)]

theorem winv_den_eval {σ₀ : K} {D : ℕ} {P Q : K[X]} (hQ : Q.natDegree ≤ D) {w : K} (hw : w ≠ 0) :
    (winv σ₀ D P Q).den.eval w = w ^ D * Q.eval (σ₀ / w) := by
  rw [winv]; exact homog_eval_ne_zero hQ hw

theorem winv_den_eval_zero (σ₀ : K) (P Q : K[X]) : (winv σ₀ Q.natDegree P Q).den.eval 0 = Q.leadingCoeff * σ₀ ^ Q.natDegree := by
  rw [winv]; exact homog_eval_zero σ₀ _ Q

theorem winv_evalAt_zero (σ₀ : K) {P Q : K[X]} (hP : P.natDegree < Q.natDegree) : (winv σ₀ Q.natDegree P Q).evalAt 0 = 0 := by
  rw [RatPair.evalAt, winv, homog_eval_zero, coeff_eq_zero_of_natDegree_lt hP, zero_mul, zero_div]

end IdAnn

namespace IdAnn

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

section Core

variable [IsAlgClosed K]

theorem core1 (NA DA NB DB : K[X]) (hDA : DA ≠ 0) (hDB : DB ≠ 0)
    (horth : gauss (NA * DB + NB * DA) = max (gauss (NA * DB)) (gauss (NB * DA)))
    (Bad : Multiset K) {ε : Γ₀}
    (hbound : ∀ y : K, v y = 1 → (∀ b ∈ Bad, v b ≤ 1 → 1 ≤ v (y - b)) →
      v ((NA * DB + NB * DA).eval y / (DA.eval y * DB.eval y)) < ε) :
    gauss NA < ε * gauss DA ∧ gauss NB < ε * gauss DB := by
  set N := NA * DB + NB * DA with hN
  obtain ⟨y, hy1, hygen⟩ := exists_generic ((0 : K) ::ₘ (Bad + N.roots + DA.roots + DB.roots))
  have hy : v y = 1 := le_antisymm hy1 (by simpa using hygen 0 (Multiset.mem_cons_self _ _) (by simp))
  have hb := hbound y hy fun b hb hb1 => hygen b (Multiset.mem_cons_of_mem (by simp [hb])) hb1
  have hvN : v (N.eval y) = gauss N := v_eval_eq_gauss N hy1 fun α hα => hygen α (Multiset.mem_cons_of_mem (by simp [hα]))
  have hvA : v (DA.eval y) = gauss DA := v_eval_eq_gauss DA hy1 fun α hα => hygen α (Multiset.mem_cons_of_mem (by simp [hα]))
  have hvB : v (DB.eval y) = gauss DB := v_eval_eq_gauss DB hy1 fun α hα => hygen α (Multiset.mem_cons_of_mem (by simp [hα]))
  rw [map_div₀, map_mul, hvN, hvA, hvB, div_lt_iff₀ (mul_pos (gauss_pos hDA) (gauss_pos hDB))] at hb
  have hA' : gauss NA * gauss DB ≤ gauss N := by rw [← gauss_mul, horth]; exact le_max_left _ _
  have hB' : gauss NB * gauss DA ≤ gauss N := by rw [← gauss_mul, horth]; exact le_max_right _ _
  constructor
  · have : gauss NA * gauss DB < ε * gauss DA * gauss DB := by rw [mul_assoc]; exact hA'.trans_lt hb
    exact lt_of_mul_lt_mul_right' this
  · have : gauss NB * gauss DA < ε * gauss DB * gauss DA := by
      rw [mul_assoc, mul_comm (gauss DB)]; exact hB'.trans_lt hb
    exact lt_of_mul_lt_mul_right' this

theorem core_outer (NA DA NB DB : K[X]) (hDA : DA ≠ 0) (hDB : DB ≠ 0) (hdeg : NA.degree < DA.degree)
    (hA : ∀ α ∈ DA.roots, v α < 1) (hB : ∀ β ∈ DB.roots, 1 ≤ v β)
    (Bad : Multiset K) {ε : Γ₀}
    (hbound : ∀ y : K, v y = 1 → (∀ b ∈ Bad, v b ≤ 1 → 1 ≤ v (y - b)) →
      v ((NA * DB + NB * DA).eval y / (DA.eval y * DB.eval y)) < ε) :
    gauss NA < ε * gauss DA ∧ gauss NB < ε * gauss DB :=
  core1 NA DA NB DB hDA hDB (orth_outer NA DA NB DB hDA hDB hdeg hA hB) Bad hbound

omit [IsAlgClosed K] in

theorem eval_comp_C_mul_X (P : K[X]) (σ₀ y' : K) : (P.comp (C σ₀ * X)).eval y' = P.eval (σ₀ * y') := by
  rw [eval_comp, eval_mul, eval_C, eval_X]

omit [IsAlgClosed K] in
theorem roots_comp_C_mul_X {P : K[X]} (hP : P ≠ 0) {σ₀ : K} (hσ : σ₀ ≠ 0) {α' : K}
    (h : α' ∈ (P.comp (C σ₀ * X)).roots) : σ₀ * α' ∈ P.roots := by
  have hne : P.comp (C σ₀ * X) ≠ 0 := by
    rw [Ne, comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_of_ne_zero hσ)]; exact hP
  have := (mem_roots hne).1 h
  rw [IsRoot.def, eval_comp_C_mul_X] at this
  exact (mem_roots hP).2 this

theorem core_inner (σ₀ : K) (hσ0 : σ₀ ≠ 0) (hσ1 : v σ₀ < 1)
    (NA DA NB DB : K[X]) (hDA : DA ≠ 0) (hDB : DB ≠ 0) (hdeg : NA.degree < DA.degree)
    (hA : ∀ α ∈ DA.roots, v α ≤ v σ₀) (hB : ∀ β ∈ DB.roots, 1 ≤ v β)
    (Bad : Multiset K) {ε : Γ₀}
    (hbound : ∀ y : K, v y = v σ₀ → (∀ b ∈ Bad, v b ≤ v σ₀ → v σ₀ ≤ v (y - b)) →
      v ((NA * DB + NB * DA).eval y / (DA.eval y * DB.eval y)) < ε) :
    gauss (NA.comp (C σ₀ * X)) < ε * gauss (DA.comp (C σ₀ * X)) ∧
      gauss (NB.comp (C σ₀ * X)) < ε * gauss (DB.comp (C σ₀ * X)) := by
  have hvσ : 0 < v σ₀ := (Valuation.pos_iff _).2 hσ0
  have hnz : σ₀ ∈ nonZeroDivisors K := mem_nonZeroDivisors_of_ne_zero hσ0
  set q : K[X] := C σ₀ * X with hq
  have hDA' : DA.comp q ≠ 0 := by rw [hq, Ne, comp_C_mul_X_eq_zero_iff hnz]; exact hDA
  have hDB' : DB.comp q ≠ 0 := by rw [hq, Ne, comp_C_mul_X_eq_zero_iff hnz]; exact hDB
  have hdegq : q.degree = 1 := by rw [hq]; exact degree_C_mul_X hσ0
  have hdeg' : (NA.comp q).degree < (DA.comp q).degree := by
    rw [degree_comp (by rw [hdegq]; exact zero_lt_one), degree_comp (by rw [hdegq]; exact zero_lt_one), hdegq,
      mul_one, mul_one]
    exact hdeg
  have hA' : ∀ α ∈ (DA.comp q).roots, v α ≤ 1 := fun α hα => by
    have := hA _ (roots_comp_C_mul_X hDA hσ0 (hq ▸ hα))
    rw [map_mul] at this
    calc v α = (v σ₀)⁻¹ * (v σ₀ * v α) := by rw [← mul_assoc, inv_mul_cancel₀ hvσ.ne', one_mul]
      _ ≤ (v σ₀)⁻¹ * v σ₀ := mul_le_mul' le_rfl this
      _ = 1 := inv_mul_cancel₀ hvσ.ne'
  have hB' : ∀ β ∈ (DB.comp q).roots, 1 < v β := fun β hβ => by
    have := hB _ (roots_comp_C_mul_X hDB hσ0 (hq ▸ hβ))
    rw [map_mul] at this
    by_contra hle
    push Not at hle
    have : v σ₀ * v β < 1 := (mul_le_mul' le_rfl hle).trans_lt (by rwa [mul_one])
    exact absurd ‹1 ≤ v σ₀ * v β› this.not_ge
  have horth := orth_inner (NA.comp q) (DA.comp q) (NB.comp q) (DB.comp q) hDA' hDB' hdeg' hA' hB'
  refine core1 (NA.comp q) (DA.comp q) (NB.comp q) (DB.comp q) hDA' hDB' horth (Bad.map fun b => b / σ₀) ?_
  intro y' hy' hgen'
  have key : (NA.comp q * DB.comp q + NB.comp q * DA.comp q).eval y' / ((DA.comp q).eval y' * (DB.comp q).eval y') =
      (NA * DB + NB * DA).eval (σ₀ * y') / (DA.eval (σ₀ * y') * DB.eval (σ₀ * y')) := by
    simp only [hq, eval_add, eval_mul, eval_comp_C_mul_X]
  rw [key]
  refine hbound (σ₀ * y') (by rw [map_mul, hy', mul_one]) fun b hb hbσ => ?_
  have h1 : 1 ≤ v (y' - b / σ₀) := by
    refine hgen' _ (Multiset.mem_map_of_mem _ hb) ?_
    rw [map_div₀, div_le_iff₀ hvσ, one_mul]; exact hbσ
  have : σ₀ * y' - b = σ₀ * (y' - b / σ₀) := by field_simp
  rw [this, map_mul]
  exact le_mul_of_one_le_right' h1

end Core

end IdAnn

namespace Z1

open IdAnn Polynomial CerednikDrinfeld.Omega

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

theorem v_sub_eq_of_lt {x y : K} (h : v y < v x) : v (x - y) = v x := by
  rw [sub_eq_add_neg]; apply Valuation.map_add_eq_of_lt_left; rwa [Valuation.map_neg]

theorem v_eq_of_v_sub_lt {a b : K} (h : v (a - b) < v b) : v a = v b := by
  have e : a = b + (a - b) := by ring
  rw [e]; exact Valuation.map_add_eq_of_lt_left _ h

def InF (c π : K) (Z : Finset K) (z : K) : Prop := v (z - c) ≤ v π ∧ ∀ ζ ∈ Z, v π ≤ v (z - ζ)

theorem inF_of_v_sub_lt {c π : K} {Z : Finset K} {z w : K} (hz : InF c π Z z) (hw : v (w - z) < v π) : InF c π Z w := by
  refine ⟨?_, fun ζ hζ => ?_⟩
  · have e : w - c = (w - z) + (z - c) := by ring
    rw [e]; exact (Valuation.map_add _ _ _).trans (max_le hw.le hz.1)
  · have h1 := hz.2 ζ hζ
    have e : w - ζ = (z - ζ) - (z - w) := by ring
    rw [e, v_sub_eq_of_lt (by rw [Valuation.map_sub_swap]; exact hw.trans_le h1)]
    exact h1

theorem v_sub_le_of_not_lt {c α z w : K} {ρ : Γ₀} (hz : v (z - c) ≤ ρ) (hzα : ¬ v (z - α) < ρ) (hw : v (w - c) ≤ ρ) :
    v (w - α) ≤ v (z - α) := by
  rw [not_lt] at hzα
  rcases le_or_gt (v (α - c)) ρ with hα | hα
  · have e : w - α = (w - c) - (α - c) := by ring
    rw [e]; exact ((Valuation.map_sub _ _ _).trans (max_le hw hα)).trans hzα
  · have e1 : v (w - α) = v (α - c) := by
      have e : w - α = (w - c) - (α - c) := by ring
      rw [e, Valuation.map_sub_swap, v_sub_eq_of_lt (hw.trans_lt hα)]
    have e2 : v (z - α) = v (α - c) := by
      have e : z - α = (z - c) - (α - c) := by ring
      rw [e, Valuation.map_sub_swap, v_sub_eq_of_lt (hz.trans_lt hα)]
    rw [e1, e2]

variable [IsAlgClosed K]

theorem v_eval_le_of_generic (P : K[X]) {c z w : K} {ρ : Γ₀} (hz : v (z - c) ≤ ρ)
    (hgen : ∀ α ∈ P.roots, ¬ v (z - α) < ρ) (hw : v (w - c) ≤ ρ) :
    v (P.eval w) ≤ v (P.eval z) := by
  conv_lhs => rw [eq_C_mul_prod P]
  conv_rhs => rw [eq_C_mul_prod P]
  simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, map_mul, map_multiset_prod]
  refine mul_le_mul' le_rfl (Multiset.prod_map_le_prod_map _ _ fun α hα => ?_)
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
  exact v_sub_le_of_not_lt hz (hgen α hα) hw

theorem v_eval_eq_of_generic (P : K[X]) {c z w : K} {ρ : Γ₀} (hz : v (z - c) ≤ ρ)
    (hgz : ∀ α ∈ P.roots, ¬ v (z - α) < ρ) (hw : v (w - c) ≤ ρ) (hgw : ∀ α ∈ P.roots, ¬ v (w - α) < ρ) :
    v (P.eval w) = v (P.eval z) :=
  le_antisymm (v_eval_le_of_generic P hz hgz hw) (v_eval_le_of_generic P hw hgw hz)

theorem exists_generic_disc (c π : K) (hπ : π ≠ 0) (B : Multiset K) :
    ∃ y : K, v (y - c) ≤ v π ∧ ∀ b ∈ B, v π ≤ v (y - b) := by
  have hvπ : 0 < v π := (Valuation.pos_iff _).mpr hπ
  obtain ⟨y', hy', hgen⟩ := exists_generic (B.map fun b => (b - c) / π)
  refine ⟨π * y' + c, ?_, fun b hb => ?_⟩
  · rw [add_sub_cancel_right, map_mul]
    calc v π * v y' ≤ v π * 1 := mul_le_mul' le_rfl hy'
      _ = v π := mul_one _
  · have e : π * y' + c - b = π * (y' - (b - c) / π) := by
      rw [mul_sub, mul_div_cancel₀ _ hπ]; ring
    rw [e, map_mul]
    have hmem : (b - c) / π ∈ B.map fun b => (b - c) / π := Multiset.mem_map_of_mem _ hb
    rcases le_or_gt (v ((b - c) / π)) 1 with h1 | h1
    · exact le_mul_of_one_le_right' (hgen _ hmem h1)
    · have : v (y' - (b - c) / π) = v ((b - c) / π) := by
        rw [Valuation.map_sub_swap, v_sub_eq_of_lt (hy'.trans_lt h1)]
      rw [this]
      exact le_mul_of_one_le_right' h1.le

end Z1

open IdAnn Polynomial CerednikDrinfeld.Omega in
theorem solution
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (S : Set K) (c π : K) (hπ : π ≠ 0) (Z : Finset K) (hZ : ∀ ζ ∈ Z, Valued.v π ≤ Valued.v (c - ζ))
    (hS : ∀ z : K, Valued.v (z - c) ≤ Valued.v π → (∀ ζ ∈ Z, Valued.v π ≤ Valued.v (z - ζ)) → z ∈ S)
    {f : ↥S → K} (hf : f ∈ holOn K S) :
    (∀ z : ↥S, Valued.v ((z : K) - c) ≤ Valued.v π → (∀ ζ ∈ Z, Valued.v π ≤ Valued.v ((z : K) - ζ)) → f z = 0) ∨
      Set.Finite {z : ↥S | Valued.v ((z : K) - c) ≤ Valued.v π ∧
        (∀ ζ ∈ Z, Valued.v π ≤ Valued.v ((z : K) - ζ)) ∧ f z = 0} := by
  classical

  by_cases hall : ∀ z : ↥S, Z1.InF c π Z (z : K) → f z = 0
  · exact Or.inl fun z h1 h2 => hall z ⟨h1, h2⟩
  right
  push Not at hall
  obtain ⟨z₁, hz₁F, hfz₁⟩ := hall
  have hvπ : 0 < Valued.v π := (Valuation.pos_iff _).mpr hπ

  obtain ⟨r, hpf, ⟨b, hb⟩, hlim⟩ := (mem_holOn_iff (K := K) f).mp hf
  have hm0 : vRestrict K (f z₁) ≠ 0 := (Valuation.ne_zero_iff _).mpr hfz₁
  rw [tendstoUniformly_iff_vRestrict] at hlim
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 (hlim (Units.mk0 _ hm0))
  have happ : ∀ z : ↥S, Valued.v ((r k).evalAt z - f z) < Valued.v (f z₁) := fun z =>
    (v_lt_iff_vRestrict_lt K _ _).2 (by simpa only [Units.val_mk0] using hk k le_rfl z)
  set P : K[X] := (r k).num with hP
  set Q : K[X] := (r k).den with hQ
  have hrz : ∀ z : K, (r k).evalAt z = P.eval z / Q.eval z := fun z => rfl

  have hQz₁ : Q.eval (z₁ : K) ≠ 0 := hpf k z₁ z₁.2
  have hQ0 : Q ≠ 0 := fun h => hQz₁ (by rw [h, eval_zero])
  have hrz₁ : Valued.v ((r k).evalAt z₁) = Valued.v (f z₁) := Z1.v_eq_of_v_sub_lt (happ z₁)
  have hm : 0 < Valued.v (f z₁) := (Valuation.pos_iff _).mpr hfz₁
  have hP0 : P ≠ 0 := by
    intro h
    have : (r k).evalAt z₁ = 0 := by rw [hrz, h, eval_zero, zero_div]
    rw [this, map_zero] at hrz₁
    exact hm.ne' hrz₁.symm

  have hQgen : ∀ z : K, Z1.InF c π Z z → ∀ β ∈ Q.roots, ¬ Valued.v (z - β) < Valued.v π := by
    intro z hz β hβ hlt
    have hβF : Z1.InF c π Z β := Z1.inF_of_v_sub_lt hz (by rw [Valuation.map_sub_swap]; exact hlt)
    have hβS : β ∈ S := hS β hβF.1 hβF.2
    exact hpf k β hβS ((mem_roots hQ0).1 hβ)

  obtain ⟨y, hyc, hygen⟩ := Z1.exists_generic_disc c π hπ (Z.val + P.roots + Q.roots)
  have hyF : Z1.InF c π Z y := ⟨hyc, fun ζ hζ => hygen ζ (Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inl hζ))))⟩
  have hyP : ∀ α ∈ P.roots, ¬ Valued.v (y - α) < Valued.v π := fun α hα =>
    not_lt.mpr (hygen α (Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr hα)))))
  have hyQ : ∀ β ∈ Q.roots, ¬ Valued.v (y - β) < Valued.v π := fun β hβ =>
    not_lt.mpr (hygen β (Multiset.mem_add.mpr (Or.inr hβ)))

  have hQconst : ∀ z : K, Z1.InF c π Z z → Valued.v (Q.eval z) = Valued.v (Q.eval y) := fun z hz =>
    Z1.v_eval_eq_of_generic Q hyc hyQ hz.1 (hQgen z hz)
  have hQy0 : 0 < Valued.v (Q.eval y) := by
    rw [← hQconst z₁ hz₁F]; exact (Valuation.pos_iff _).mpr hQz₁
  have hry : Valued.v (f z₁) ≤ Valued.v ((r k).evalAt y) := by
    rw [← hrz₁, hrz, hrz, map_div₀, map_div₀, hQconst z₁ hz₁F]
    exact div_le_div_of_nonneg_right (Z1.v_eval_le_of_generic P hyc hyP hz₁F.1) zero_le'

  have hloc : ∀ z : ↥S, Z1.InF c π Z (z : K) → f z = 0 → ∃ α ∈ P.roots, Valued.v ((z : K) - α) < Valued.v π := by
    intro z hzF hfz
    by_contra hnone
    push Not at hnone
    have hPz : Valued.v (P.eval (z : K)) = Valued.v (P.eval y) :=
      Z1.v_eval_eq_of_generic P hyc hyP hzF.1 (fun α hα => not_lt.mpr (hnone α hα))
    have hrzy : Valued.v ((r k).evalAt z) = Valued.v ((r k).evalAt y) := by
      rw [hrz, hrz, map_div₀, map_div₀, hPz, hQconst z hzF]
    have h1 := happ z
    rw [hfz, sub_zero, hrzy] at h1
    exact absurd hry (not_le.mpr h1)

  have hT : ∀ α ∈ P.roots.toFinset, Set.Finite {z : ↥S | Z1.InF c π Z (z : K) ∧
      Valued.v ((z : K) - α) < Valued.v π ∧ f z = 0} := by
    intro α _
    by_cases hmeet : ∃ w : K, Z1.InF c π Z w ∧ Valued.v (w - α) < Valued.v π
    · obtain ⟨w, hwF, hwα⟩ := hmeet
      have hαF : Z1.InF c π Z α := Z1.inF_of_v_sub_lt hwF (by rw [Valuation.map_sub_swap]; exact hwα)

      set Z' : Finset K := Z.filter fun ζ => Valued.v (c - ζ) ≤ Valued.v π with hZ'
      have hZ'eq : ∀ ζ ∈ Z', Valued.v (α - ζ) = Valued.v π := by
        intro ζ hζ
        obtain ⟨hζZ, hζc⟩ := Finset.mem_filter.mp hζ
        refine le_antisymm ?_ ?_
        · have e : α - ζ = (α - c) + (c - ζ) := by ring
          rw [e]; exact (Valuation.map_add _ _ _).trans (max_le hαF.1 hζc)
        · have h1 := hwF.2 ζ hζZ
          have e : α - ζ = (w - ζ) - (w - α) := by ring
          rw [e, Z1.v_sub_eq_of_lt (hwα.trans_le h1)]
          exact h1
      have hS' : ∀ z : K, Valued.v (z - α) ≤ Valued.v π → (∀ ζ ∈ Z', Valued.v π ≤ Valued.v (z - ζ)) → z ∈ S := by
        intro z hzα hzZ'
        have hzc : Valued.v (z - c) ≤ Valued.v π := by
          have e : z - c = (z - α) + (α - c) := by ring
          rw [e]; exact (Valuation.map_add _ _ _).trans (max_le hzα hαF.1)
        refine hS z hzc fun ζ hζ => ?_
        by_cases hζc : Valued.v (c - ζ) ≤ Valued.v π
        · exact hzZ' ζ (Finset.mem_filter.mpr ⟨hζ, hζc⟩)
        · rw [not_le] at hζc
          have e : z - ζ = (c - ζ) - (c - z) := by ring
          rw [e, Z1.v_sub_eq_of_lt (by rw [Valuation.map_sub_swap]; exact hzc.trans_lt hζc)]
          exact hζc.le
      rcases CerednikDrinfeld.Omega.finite_setOf_apply_eq_zero_of_v_sub_lt_of_mem_holOn K hrk S α π hπ Z' hZ'eq hS' hf
        with hzero | hfinα
      ·
        exfalso
        apply hfz₁
        refine hzero z₁ ?_ fun ζ hζ => hz₁F.2 ζ (Finset.mem_filter.mp hζ).1
        have e : (z₁ : K) - α = ((z₁ : K) - c) - (α - c) := by ring
        rw [e]; exact (Valuation.map_sub _ _ _).trans (max_le hz₁F.1 hαF.1)
      · exact hfinα.subset fun z hz => ⟨hz.2.1, hz.2.2⟩
    ·
      refine (Set.finite_empty : (∅ : Set ↥S).Finite).subset fun z hz => ?_
      exact absurd ⟨(z : K), hz.1, hz.2.1⟩ hmeet

  refine (Set.Finite.biUnion P.roots.toFinset.finite_toSet hT).subset fun z hz => ?_
  obtain ⟨h1, h2, h3⟩ := hz
  obtain ⟨α, hα, hzα⟩ := hloc z ⟨h1, h2⟩ h3
  exact Set.mem_biUnion (Multiset.mem_toFinset.mpr hα) ⟨⟨h1, h2⟩, hzα, h3⟩

end
end S_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_disc_of_mem_holOn
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_finite_setOf_apply_eq_zero_disc_of_mem_holOn (solution)
