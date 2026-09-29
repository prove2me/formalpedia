-- Prove2me | solution 1 for CerednikDrinfeld.Omega.RatPair.identityPrinciple_annulus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/472b5eec-78c6-5dcd-89a8-56ea26bde1b5

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_CerednikDrinfeld_Omega_RatPair_identityPrinciple_disc
import Theorems.Thm_CerednikDrinfeld_Omega_gaussNorm_add_eq_max_of_separated_poles
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_RatPair_identityPrinciple_annulus

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

namespace IdAnn

open scoped Classical

structure AData (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] where

  S : Set K

  r : ℕ → RatPair K

  σ₀ : K

  Z : Finset K

  Ξ : Finset K
  hpf : ∀ k, (r k).IsPoleFreeOn S
  hσ0 : σ₀ ≠ 0
  hσ1 : Valued.v σ₀ < 1
  hZ : ∀ ζ ∈ Z, 1 ≤ Valued.v ζ
  hΞ : ∀ ξ ∈ Ξ, Valued.v ξ ≤ Valued.v σ₀
  hS : ∀ y : K, Valued.v σ₀ ≤ Valued.v y → Valued.v y ≤ 1 → (∀ ζ ∈ Z, 1 ≤ Valued.v (y - ζ)) →
    (∀ ξ ∈ Ξ, Valued.v σ₀ ≤ Valued.v (y - ξ)) → y ∈ S

namespace AData

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
variable (c : AData K)

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

def GoodOut (y : K) : Prop := v y ≤ 1 ∧ ∀ ζ ∈ c.Z, 1 ≤ v (y - ζ)

def GoodIn (y : K) : Prop := v c.σ₀ ≤ v y ∧ ∀ ξ ∈ c.Ξ, v c.σ₀ ≤ v (y - ξ)

omit [IsAlgClosed K] in
theorem memS {y : K} (ho : c.GoodOut y) (hi : c.GoodIn y) : y ∈ c.S := c.hS y hi.1 ho.1 ho.2 hi.2

omit [IsAlgClosed K] in
theorem vσ_pos : 0 < v c.σ₀ := (Valuation.pos_iff _).2 c.hσ0

omit [IsAlgClosed K] in
theorem goodOut_of_lt_one {y : K} (hy : v y < 1) : c.GoodOut y :=
  ⟨hy.le, fun ζ hζ => by rw [Valuation.map_sub_eq_of_lt_right _ (hy.trans_le (c.hZ ζ hζ))]; exact c.hZ ζ hζ⟩

omit [IsAlgClosed K] in
theorem goodOut_of_gen {y : K} (hy : v y ≤ 1) (hgen : ∀ ζ ∈ c.Z, v ζ ≤ 1 → 1 ≤ v (y - ζ)) : c.GoodOut y :=
  ⟨hy, fun ζ hζ => by
    rcases le_or_gt (v ζ) 1 with h | h
    · exact hgen ζ hζ h
    · rw [Valuation.map_sub_eq_of_lt_right _ (hy.trans_lt h)]; exact h.le⟩

omit [IsAlgClosed K] in
theorem goodIn_of_lt {y : K} (hy : v c.σ₀ < v y) : c.GoodIn y :=
  ⟨hy.le, fun ξ hξ => by rw [Valuation.map_sub_eq_of_lt_left _ ((c.hΞ ξ hξ).trans_lt hy)]; exact hy.le⟩

omit [IsAlgClosed K] in
theorem goodIn_of_eq_one {y : K} (hy : v y = 1) : c.GoodIn y := c.goodIn_of_lt (hy ▸ c.hσ1)

omit [IsAlgClosed K] in
theorem goodIn_of_gen {y : K} (hy : v y = v c.σ₀) (hgen : ∀ ξ ∈ c.Ξ, v ξ ≤ v c.σ₀ → v c.σ₀ ≤ v (y - ξ)) : c.GoodIn y :=
  ⟨hy.ge, fun ξ hξ => hgen ξ hξ (c.hΞ ξ hξ)⟩

theorem den_ne (k : ℕ) : (c.r k).den ≠ 0 := by
  obtain ⟨y, hy1, hygen⟩ := exists_generic (K := K) ((0 : K) ::ₘ c.Z.val)
  have hy : v y = 1 := le_antisymm hy1 (by simpa using hygen 0 (Multiset.mem_cons_self _ _) (by simp))
  have hyS : y ∈ c.S := c.memS (c.goodOut_of_gen hy1 fun ζ hζ h => hygen ζ (Multiset.mem_cons_of_mem hζ) h)
    (c.goodIn_of_eq_one hy)
  intro h
  exact c.hpf k y hyS (by rw [h, eval_zero])

omit [IsAlgClosed K] in
theorem root_cases (k : ℕ) {α : K} (hα : (c.r k).den.eval α = 0) : v α ≤ v c.σ₀ ∨ 1 ≤ v α := by
  by_contra h
  push Not at h
  exact c.hpf k α (c.memS (c.goodOut_of_lt_one h.2) (c.goodIn_of_lt h.1)) hα

omit [IsAlgClosed K] in
theorem outroot_gen (k : ℕ) {y : K} (hy : c.GoodOut y) {α : K} (hα : (c.r k).den.eval α = 0)
    (h1 : v c.σ₀ < v α) (h2 : v α ≤ 1) : 1 ≤ v (y - α) := by
  by_contra hlt
  push Not at hlt
  refine c.hpf k α (c.memS ⟨h2, fun ζ hζ => ?_⟩ (c.goodIn_of_lt h1)) hα
  have : α - ζ = (y - ζ) - (y - α) := by ring
  rw [this, Valuation.map_sub_eq_of_lt_left _ (hlt.trans_le (hy.2 ζ hζ))]
  exact hy.2 ζ hζ

omit [IsAlgClosed K] in
theorem inroot_gen (k : ℕ) {y : K} (hy : c.GoodIn y) {α : K} (hα : (c.r k).den.eval α = 0)
    (h : v α ≤ v c.σ₀) : v c.σ₀ ≤ v (y - α) := by
  rcases h.lt_or_eq with h | h
  · rw [Valuation.map_sub_eq_of_lt_left _ (h.trans_le hy.1)]; exact hy.1
  by_contra hlt
  push Not at hlt
  refine c.hpf k α (c.memS (c.goodOut_of_lt_one (h.trans_lt c.hσ1)) ⟨h.ge, fun ξ hξ => ?_⟩) hα
  have : α - ξ = (y - ξ) - (y - α) := by ring
  rw [this, Valuation.map_sub_eq_of_lt_left _ (hlt.trans_le (hy.2 ξ hξ))]
  exact hy.2 ξ hξ

def Qi (k : ℕ) : K[X] := Qin (v c.σ₀) (c.r k).den

def Qo (k : ℕ) : K[X] := Qout (v c.σ₀) (c.r k).den

def Ri (k : ℕ) : K[X] := inNum (v c.σ₀) (c.r k).num (c.r k).den

def Po (k : ℕ) : K[X] := outNum (v c.σ₀) (c.r k).num (c.r k).den

def fin (k : ℕ) (y : K) : K := (c.Ri k).eval y / (c.Qi k).eval y

def fout (k : ℕ) (y : K) : K := (c.Po k).eval y / (c.Qo k).eval y

omit [IsAlgClosed K] in
theorem Qi_ne (k : ℕ) : c.Qi k ≠ 0 := Qin_ne_zero _ _
theorem Qo_ne (k : ℕ) : c.Qo k ≠ 0 := Qout_ne_zero _ (c.den_ne k)
omit [IsAlgClosed K] in
theorem Qi_monic (k : ℕ) : (c.Qi k).Monic := Qin_monic _ _

omit [IsAlgClosed K] in
theorem Qi_roots (k : ℕ) : ∀ α ∈ (c.Qi k).roots, v α ≤ v c.σ₀ := fun _ hα => ((mem_roots_Qin _).1 hα).2

theorem Qo_roots (k : ℕ) : ∀ β ∈ (c.Qo k).roots, 1 ≤ v β := fun β hβ => by
  obtain ⟨h1, h2⟩ := (mem_roots_Qout _ (c.den_ne k)).1 hβ
  exact (c.root_cases k ((mem_roots (c.den_ne k)).1 h1)).resolve_left (not_le.2 h2)

theorem Qo_gen (k : ℕ) {y : K} (hy : c.GoodOut y) : ∀ β ∈ (c.Qo k).roots, v β ≤ 1 → 1 ≤ v (y - β) := fun β hβ h1 => by
  obtain ⟨hr, h2⟩ := (mem_roots_Qout _ (c.den_ne k)).1 hβ
  exact c.outroot_gen k hy ((mem_roots (c.den_ne k)).1 hr) h2 h1

theorem Qi_gen (k : ℕ) {y : K} (hy : c.GoodIn y) : ∀ α ∈ (c.Qi k).roots, v c.σ₀ ≤ v (y - α) := fun α hα => by
  obtain ⟨hr, h2⟩ := (mem_roots_Qin _).1 hα
  exact c.inroot_gen k hy ((mem_roots (c.den_ne k)).1 hr) h2

theorem Qo_eval_ne (k : ℕ) {y : K} (hy : c.GoodOut y) : (c.Qo k).eval y ≠ 0 := fun h => by
  have := c.Qo_gen k hy y ((mem_roots (c.Qo_ne k)).2 h) hy.1
  rw [sub_self, map_zero] at this
  exact not_lt_of_ge this zero_lt_one

theorem Qi_eval_ne (k : ℕ) {y : K} (hy : c.GoodIn y) : (c.Qi k).eval y ≠ 0 := fun h => by
  have := c.Qi_gen k hy y ((mem_roots (c.Qi_ne k)).2 h)
  rw [sub_self, map_zero] at this
  exact not_lt_of_ge this c.vσ_pos

theorem degree_Ri_lt (k : ℕ) : (c.Ri k).degree < (c.Qi k).degree := degree_inNum_lt _ _ _

theorem natDegree_Ri_le (k : ℕ) : (c.Ri k).natDegree ≤ (c.Qi k).natDegree := natDegree_inNum_le _ _ _

theorem split_num (k : ℕ) : c.Ri k * c.Qo k + c.Po k * c.Qi k = (c.r k).num := split_eq _ _ _
theorem split_den (k : ℕ) : c.Qi k * c.Qo k = (c.r k).den := Qin_mul_Qout _ _

theorem evalAt_eq (k : ℕ) {y : K} (hy : y ∈ c.S) : (c.r k).evalAt y = c.fin k y + c.fout k y :=
  (eval_split (v c.σ₀) (c.r k).num (c.r k).den (c.hpf k y hy)).2.2

theorem cauchy_pieces
    (hC : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ y ∈ c.S, v ((c.r k).evalAt y - (c.r j).evalAt y) < v e) :
    (∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ y : K, c.GoodOut y → v (c.fout k y - c.fout j y) < v e) ∧
    (∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ y : K, c.GoodIn y → v (c.fin k y - c.fin j y) < v e) := by

  have key : ∀ e : K, e ≠ 0 → ∀ N : ℕ, (∀ k ≥ N, ∀ j ≥ N, ∀ y ∈ c.S, v ((c.r k).evalAt y - (c.r j).evalAt y) < v e) →
      ∀ k ≥ N, ∀ j ≥ N,
      (∀ y : K, c.GoodOut y → v (c.fout k y - c.fout j y) < v e) ∧
      (∀ y : K, c.GoodIn y → v (c.fin k y - c.fin j y) < v e) := by
    intro e he N hN k hk j hj
    set NA := c.Ri k * c.Qi j - c.Ri j * c.Qi k with hNA
    set DA := c.Qi k * c.Qi j with hDA
    set NB := c.Po k * c.Qo j - c.Po j * c.Qo k with hNB
    set DB := c.Qo k * c.Qo j with hDB
    have hDAne : DA ≠ 0 := mul_ne_zero (c.Qi_ne k) (c.Qi_ne j)
    have hDBne : DB ≠ 0 := mul_ne_zero (c.Qo_ne k) (c.Qo_ne j)
    have hdegA : NA.degree < DA.degree := by
      rw [hNA, hDA, degree_mul]
      refine (degree_sub_le _ _).trans_lt (max_lt ?_ ?_)
      · rw [degree_mul]
        exact WithBot.add_lt_add_right (degree_eq_bot.not.2 (c.Qi_ne j)) (c.degree_Ri_lt k)
      · rw [degree_mul, add_comm]
        exact WithBot.add_lt_add_left (degree_eq_bot.not.2 (c.Qi_ne k)) (c.degree_Ri_lt j)
    have hAroots : ∀ α ∈ DA.roots, v α ≤ v c.σ₀ := fun α hα => by
      rw [hDA, roots_mul hDAne, Multiset.mem_add] at hα
      rcases hα with h | h
      · exact c.Qi_roots k α h
      · exact c.Qi_roots j α h
    have hBroots : ∀ β ∈ DB.roots, 1 ≤ v β := fun β hβ => by
      rw [hDB, roots_mul hDBne, Multiset.mem_add] at hβ
      rcases hβ with h | h
      · exact c.Qo_roots k β h
      · exact c.Qo_roots j β h
    have hval : ∀ y ∈ c.S, (NA * DB + NB * DA).eval y / (DA.eval y * DB.eval y) =
        (c.r k).evalAt y - (c.r j).evalAt y := fun y hy => by
      obtain ⟨hik, hok, hk'⟩ := eval_split (v c.σ₀) (c.r k).num (c.r k).den (c.hpf k y hy)
      obtain ⟨hij, hoj, hj'⟩ := eval_split (v c.σ₀) (c.r j).num (c.r j).den (c.hpf j y hy)
      rw [RatPair.evalAt, RatPair.evalAt, hk', hj']
      change _ = (c.Ri k).eval y / (c.Qi k).eval y + (c.Po k).eval y / (c.Qo k).eval y -
        ((c.Ri j).eval y / (c.Qi j).eval y + (c.Po j).eval y / (c.Qo j).eval y)
      change (c.Qi k).eval y ≠ 0 at hik
      change (c.Qo k).eval y ≠ 0 at hok
      change (c.Qi j).eval y ≠ 0 at hij
      change (c.Qo j).eval y ≠ 0 at hoj
      rw [hNA, hDA, hNB, hDB]
      simp only [eval_add, eval_sub, eval_mul]
      field_simp
      ring
    constructor
    ·
      have hcore := (core_outer NA DA NB DB hDAne hDBne hdegA (fun α hα => (hAroots α hα).trans_lt c.hσ1) hBroots
        c.Z.val (ε := v e) fun y hy hgen => ?_).2
      · intro y hyo
        have hval' : c.fout k y - c.fout j y = NB.eval y / DB.eval y := by
          rw [fout, fout, hNB, hDB, eval_sub, eval_mul, eval_mul, eval_mul,
            div_sub_div _ _ (c.Qo_eval_ne k hyo) (c.Qo_eval_ne j hyo)]
          congr 1; ring
        rw [hval']
        refine (v_div_le_out NB DB hyo.1 fun β hβ hβ1 => ?_).trans_lt ?_
        · rw [hDB, roots_mul hDBne, Multiset.mem_add] at hβ
          rcases hβ with h | h
          · exact c.Qo_gen k hyo β h hβ1
          · exact c.Qo_gen j hyo β h hβ1
        · rw [div_lt_iff₀ (gauss_pos hDBne)]; exact hcore
      · rw [hval y (c.memS (c.goodOut_of_gen hy.le hgen) (c.goodIn_of_eq_one hy))]
        exact hN k hk j hj y (c.memS (c.goodOut_of_gen hy.le hgen) (c.goodIn_of_eq_one hy))
    ·
      have hcore := (core_inner c.σ₀ c.hσ0 c.hσ1 NA DA NB DB hDAne hDBne hdegA hAroots hBroots
        c.Ξ.val (ε := v e) fun y hy hgen => ?_).1
      · intro y hyi
        have hval' : c.fin k y - c.fin j y = NA.eval y / DA.eval y := by
          rw [fin, fin, hNA, hDA, eval_sub, eval_mul, eval_mul, eval_mul,
            div_sub_div _ _ (c.Qi_eval_ne k hyi) (c.Qi_eval_ne j hyi)]
          congr 1; ring
        rw [hval']
        have hdeg' : NA.natDegree ≤ DA.natDegree := by
          by_cases h : NA = 0
          · rw [h, natDegree_zero]; exact Nat.zero_le _
          · exact (natDegree_lt_natDegree h hdegA).le
        refine (v_div_le_in c.σ₀ c.hσ0 NA DA hDAne hdeg' hAroots hyi.1 fun α hα => ?_).trans_lt ?_
        · rw [hDA, roots_mul hDAne, Multiset.mem_add] at hα
          rcases hα with h | h
          · exact c.Qi_gen k hyi α h
          · exact c.Qi_gen j hyi α h
        · rw [div_lt_iff₀ (gauss_pos _)]
          · exact hcore
          · rw [Ne, comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_of_ne_zero c.hσ0)]; exact hDAne
      · have hyS : y ∈ c.S := c.memS (c.goodOut_of_lt_one (hy.trans_lt c.hσ1)) (c.goodIn_of_gen hy hgen)
        rw [hval y hyS]
        exact hN k hk j hj y hyS
  constructor
  · intro e he
    obtain ⟨N, hN⟩ := hC e he
    exact ⟨N, fun k hk j hj => (key e he N hN k hk j hj).1⟩
  · intro e he
    obtain ⟨N, hN⟩ := hC e he
    exact ⟨N, fun k hk j hj => (key e he N hN k hk j hj).2⟩

end AData

end IdAnn

namespace IdAnn

open scoped Classical

namespace AData

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
variable (c : AData K)

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

theorem outer_limits
    (h0 : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y : K, v y = 1 → (∀ ζ ∈ c.Z, 1 ≤ v (y - ζ)) → v ((c.r k).evalAt y) < v e) :
    (∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y : K, c.GoodOut y → v (c.fout k y) < v e) ∧
    (∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y : K, 1 ≤ v y → v (c.fin k y) < v e) := by
  have key : ∀ e : K, e ≠ 0 → ∀ N : ℕ,
      (∀ k ≥ N, ∀ y : K, v y = 1 → (∀ ζ ∈ c.Z, 1 ≤ v (y - ζ)) → v ((c.r k).evalAt y) < v e) → ∀ k ≥ N,
      (∀ y : K, c.GoodOut y → v (c.fout k y) < v e) ∧ (∀ y : K, 1 ≤ v y → v (c.fin k y) < v e) := by
    intro e he N hN k hk
    have hcore := core_outer (c.Ri k) (c.Qi k) (c.Po k) (c.Qo k) (c.Qi_ne k) (c.Qo_ne k) (c.degree_Ri_lt k)
      (fun α hα => (c.Qi_roots k α hα).trans_lt c.hσ1) (c.Qo_roots k) c.Z.val (ε := v e) fun y hy hgen => by
        have ho : c.GoodOut y := c.goodOut_of_gen hy.le hgen
        rw [c.split_num, ← eval_mul, c.split_den]
        exact hN k hk y hy ho.2
    constructor
    · intro y hyo
      rw [fout]
      refine (v_div_le_out _ _ hyo.1 (c.Qo_gen k hyo)).trans_lt ?_
      rw [div_lt_iff₀ (gauss_pos (c.Qo_ne k))]; exact hcore.2
    · intro y hy1
      rw [fin]
      have h := v_div_le_in (1 : K) one_ne_zero (c.Ri k) (c.Qi k) (c.Qi_ne k) (c.natDegree_Ri_le k)
        (fun α hα => by rw [map_one]; exact (c.Qi_roots k α hα).trans c.hσ1.le) (y := y) (by rwa [map_one])
        (fun α hα => by
          rw [map_one, Valuation.map_sub_eq_of_lt_left _ (((c.Qi_roots k α hα).trans_lt c.hσ1).trans_le hy1)]
          exact hy1)
      rw [C_1, one_mul, comp_X, comp_X] at h
      refine h.trans_lt ?_
      rw [div_lt_iff₀ (gauss_pos (c.Qi_ne k))]; exact hcore.1
  constructor
  · intro e he
    obtain ⟨N, hN⟩ := h0 e he
    exact ⟨N, fun k hk => (key e he N hN k hk).1⟩
  · intro e he
    obtain ⟨N, hN⟩ := h0 e he
    exact ⟨N, fun k hk => (key e he N hN k hk).2⟩

theorem inner_limits
    (h0 : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y : K, v y = v c.σ₀ → (∀ ξ ∈ c.Ξ, v c.σ₀ ≤ v (y - ξ)) →
      v ((c.r k).evalAt y) < v e) :
    (∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y : K, c.GoodIn y → v (c.fin k y) < v e) ∧
    (∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y : K, v y ≤ v c.σ₀ → v (c.fout k y) < v e) := by
  have hnz : c.σ₀ ∈ nonZeroDivisors K := mem_nonZeroDivisors_of_ne_zero c.hσ0
  have key : ∀ e : K, e ≠ 0 → ∀ N : ℕ,
      (∀ k ≥ N, ∀ y : K, v y = v c.σ₀ → (∀ ξ ∈ c.Ξ, v c.σ₀ ≤ v (y - ξ)) → v ((c.r k).evalAt y) < v e) → ∀ k ≥ N,
      (∀ y : K, c.GoodIn y → v (c.fin k y) < v e) ∧ (∀ y : K, v y ≤ v c.σ₀ → v (c.fout k y) < v e) := by
    intro e he N hN k hk
    have hcore := core_inner c.σ₀ c.hσ0 c.hσ1 (c.Ri k) (c.Qi k) (c.Po k) (c.Qo k) (c.Qi_ne k) (c.Qo_ne k)
      (c.degree_Ri_lt k) (c.Qi_roots k) (c.Qo_roots k) c.Ξ.val (ε := v e) fun y hy hgen => by
        have hi : c.GoodIn y := c.goodIn_of_gen hy hgen
        rw [c.split_num, ← eval_mul, c.split_den]
        exact hN k hk y hy hi.2
    constructor
    · intro y hyi
      rw [fin]
      refine (v_div_le_in c.σ₀ c.hσ0 _ _ (c.Qi_ne k) (c.natDegree_Ri_le k) (c.Qi_roots k) hyi.1
        (c.Qi_gen k hyi)).trans_lt ?_
      rw [div_lt_iff₀ (gauss_pos _)]
      · exact hcore.1
      · rw [Ne, comp_C_mul_X_eq_zero_iff hnz]; exact c.Qi_ne k
    · intro y hyσ
      set y' := y / c.σ₀ with hy'
      have hyy : c.σ₀ * y' = y := by rw [hy']; field_simp [c.hσ0]
      have hvy' : v y' ≤ 1 := by
        rw [hy', map_div₀, div_le_iff₀ c.vσ_pos, one_mul]; exact hyσ
      have hQ'ne : (c.Qo k).comp (C c.σ₀ * X) ≠ 0 := by
        rw [Ne, comp_C_mul_X_eq_zero_iff hnz]; exact c.Qo_ne k
      rw [fout, ← hyy, ← eval_comp_C_mul_X, ← eval_comp_C_mul_X]
      refine (v_div_le_out _ _ hvy' fun β hβ hβ1 => ?_).trans_lt ?_
      ·
        exfalso
        have h1 := c.Qo_roots k _ (roots_comp_C_mul_X (c.Qo_ne k) c.hσ0 hβ)
        rw [map_mul] at h1
        have : v c.σ₀ * v β < 1 := (mul_le_mul' le_rfl hβ1).trans_lt (by rw [mul_one]; exact c.hσ1)
        exact absurd h1 this.not_ge
      · rw [div_lt_iff₀ (gauss_pos hQ'ne)]; exact hcore.2
  constructor
  · intro e he
    obtain ⟨N, hN⟩ := h0 e he
    exact ⟨N, fun k hk => (key e he N hN k hk).1⟩
  · intro e he
    obtain ⟨N, hN⟩ := h0 e he
    exact ⟨N, fun k hk => (key e he N hN k hk).2⟩

theorem fout_zero
    (hCout : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ y : K, c.GoodOut y → v (c.fout k y - c.fout j y) < v e)
    (hsmall : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y : K, v y ≤ v c.σ₀ → v (c.fout k y) < v e) :
    ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y : K, c.GoodOut y → v (c.fout k y) < v e := by
  let S' : Set K := {y | c.GoodOut y}
  let r' : ℕ → RatPair K := fun k => ⟨c.Po k, c.Qo k⟩
  have hev : ∀ k y, (r' k).evalAt y = c.fout k y := fun k y => rfl
  have h := L0 S' r' (fun k y hy => c.Qo_eval_ne k hy) c.Z c.hZ (fun y hy hyZ => (⟨hy, hyZ⟩ : c.GoodOut y))
    (fun e he => by
      obtain ⟨N, hN⟩ := hCout e he
      exact ⟨N, fun k hk j hj y hy => by rw [hev, hev]; exact hN k hk j hj y hy⟩)
    c.σ₀ c.hσ0
    (fun e he => by
      obtain ⟨N, hN⟩ := hsmall e he
      exact ⟨N, fun k hk y _ hyσ => by rw [hev]; exact hN k hk y hyσ⟩)
  intro e he
  obtain ⟨N, hN⟩ := h e he
  exact ⟨N, fun k hk y hy => by rw [← hev]; exact hN k hk y hy hy.1 hy.2⟩

def W (k : ℕ) : RatPair K := winv c.σ₀ (c.Qi k).natDegree (c.Ri k) (c.Qi k)

def Ξw : Finset K := (c.Ξ.filter fun ξ => v ξ = v c.σ₀).image fun ξ => c.σ₀ / ξ

def Sw : Set K := {w | v w ≤ 1 ∧ ∀ ξ' ∈ c.Ξw, 1 ≤ v (w - ξ')}

omit [IsAlgClosed K] in
theorem mem_Ξw {ξ' : K} : ξ' ∈ c.Ξw ↔ ∃ ξ ∈ c.Ξ, v ξ = v c.σ₀ ∧ c.σ₀ / ξ = ξ' := by
  simp only [Ξw, Finset.mem_image, Finset.mem_filter, and_assoc]

omit [IsAlgClosed K] in

theorem goodIn_of_Sw {w : K} (hw : w ∈ c.Sw) (hw0 : w ≠ 0) : c.GoodIn (c.σ₀ / w) := by
  have hvw : 0 < v w := (Valuation.pos_iff _).2 hw0
  have hvy : v c.σ₀ ≤ v (c.σ₀ / w) := by
    rw [map_div₀, le_div_iff₀ hvw]; exact mul_le_of_le_one_right' hw.1
  refine ⟨hvy, fun ξ hξ => ?_⟩
  rcases (c.hΞ ξ hξ).lt_or_eq with hlt | heq
  · rw [Valuation.map_sub_eq_of_lt_left _ (hlt.trans_le hvy)]; exact hvy
  · have hξ0 : ξ ≠ 0 := fun h => by rw [h, map_zero] at heq; exact c.vσ_pos.ne' heq.symm
    have hmem : c.σ₀ / ξ ∈ c.Ξw := c.mem_Ξw.2 ⟨ξ, hξ, heq, rfl⟩
    have h1 := hw.2 _ hmem
    have hid : c.σ₀ / w - ξ = ξ * (w - c.σ₀ / ξ) * (-w⁻¹) := by
      field_simp
      ring
    rw [hid, map_mul, map_mul, heq, Valuation.map_neg, map_inv₀]
    calc v c.σ₀ = v c.σ₀ * 1 * 1 := by rw [mul_one, mul_one]
      _ ≤ v c.σ₀ * v (w - c.σ₀ / ξ) * (v w)⁻¹ := mul_le_mul' (mul_le_mul' le_rfl h1) ((one_le_inv₀ hvw).2 hw.1)

end AData

end IdAnn

namespace IdAnn

open scoped Classical

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem winv_evalAt_zero' (σ₀ : K) {P Q : K[X]} (h : P.degree < Q.degree) :
    (winv σ₀ Q.natDegree P Q).evalAt 0 = 0 := by
  by_cases hP : P = 0
  · rw [RatPair.evalAt, winv, homog_eval_zero, hP, coeff_zero, zero_mul, zero_div]
  · exact winv_evalAt_zero σ₀ (natDegree_lt_natDegree hP h)

namespace AData

variable [IsAlgClosed K] (c : AData K)

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

theorem fin_zero
    (hCin : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ y : K, c.GoodIn y → v (c.fin k y - c.fin j y) < v e)
    (hsmall : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y : K, 1 ≤ v y → v (c.fin k y) < v e) :
    ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y : K, c.GoodIn y → v (c.fin k y) < v e := by
  have hW0 : ∀ k, (c.W k).evalAt 0 = 0 := fun k => winv_evalAt_zero' c.σ₀ (c.degree_Ri_lt k)
  have hWne : ∀ k (w : K), w ≠ 0 → (c.W k).evalAt w = c.fin k (c.σ₀ / w) := fun k w hw =>
    winv_evalAt (c.natDegree_Ri_le k) le_rfl hw
  have hpf : ∀ k, (c.W k).IsPoleFreeOn c.Sw := fun k w hw => by
    by_cases hw0 : w = 0
    · rw [hw0, W, winv_den_eval_zero, (c.Qi_monic k).leadingCoeff, one_mul]; exact pow_ne_zero _ c.hσ0
    · rw [W, winv_den_eval le_rfl hw0]
      exact mul_ne_zero (pow_ne_zero _ hw0) (c.Qi_eval_ne k (c.goodIn_of_Sw hw hw0))
  have hZw : ∀ ξ' ∈ c.Ξw, 1 ≤ v ξ' := fun ξ' hξ' => by
    obtain ⟨ξ, -, hvξ, rfl⟩ := c.mem_Ξw.1 hξ'
    rw [map_div₀, hvξ, div_self c.vσ_pos.ne']
  have hSw : ∀ w : K, v w ≤ 1 → (∀ ξ' ∈ c.Ξw, 1 ≤ v (w - ξ')) → w ∈ c.Sw := fun w h1 h2 => ⟨h1, h2⟩
  have hCw : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ w ∈ c.Sw,
      v ((c.W k).evalAt w - (c.W j).evalAt w) < v e := fun e he => by
    obtain ⟨N, hN⟩ := hCin e he
    refine ⟨N, fun k hk j hj w hw => ?_⟩
    by_cases hw0 : w = 0
    · rw [hw0, hW0, hW0, sub_zero, map_zero]; exact (Valuation.pos_iff _).2 he
    · rw [hWne k w hw0, hWne j w hw0]; exact hN k hk j hj _ (c.goodIn_of_Sw hw hw0)
  have h0w : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ w ∈ c.Sw, v w ≤ v c.σ₀ → v ((c.W k).evalAt w) < v e :=
    fun e he => by
    obtain ⟨N, hN⟩ := hsmall e he
    refine ⟨N, fun k hk w _ hwσ => ?_⟩
    by_cases hw0 : w = 0
    · rw [hw0, hW0, map_zero]; exact (Valuation.pos_iff _).2 he
    · rw [hWne k w hw0]
      refine hN k hk _ ?_
      rw [map_div₀, le_div_iff₀ ((Valuation.pos_iff _).2 hw0), one_mul]; exact hwσ
  have hL := L0 c.Sw (fun k => c.W k) hpf c.Ξw hZw hSw hCw c.σ₀ c.hσ0 h0w
  intro e he
  obtain ⟨N, hN⟩ := hL e he
  refine ⟨N, fun k hk y hy => ?_⟩
  have hvy : 0 < v y := c.vσ_pos.trans_le hy.1
  have hy0 : y ≠ 0 := (Valuation.pos_iff _).1 hvy
  set w := c.σ₀ / y with hw
  have hw0 : w ≠ 0 := div_ne_zero c.hσ0 hy0
  have hyw : c.σ₀ / w = y := by rw [hw, div_div_eq_mul_div, mul_div_assoc, mul_div_cancel₀ _ c.hσ0]
  have hvw : v w ≤ 1 := by rw [hw, map_div₀, div_le_iff₀ hvy, one_mul]; exact hy.1
  have hwgen : ∀ ξ' ∈ c.Ξw, 1 ≤ v (w - ξ') := fun ξ' hξ' => by
    obtain ⟨ξ, hξ, hvξ, rfl⟩ := c.mem_Ξw.1 hξ'
    have hξ0 : ξ ≠ 0 := fun h => by rw [h, map_zero] at hvξ; exact c.vσ_pos.ne' hvξ.symm
    have hyξ : v y ≤ v (y - ξ) := by
      rcases hy.1.lt_or_eq with hlt | heq
      · rw [Valuation.map_sub_eq_of_lt_left _ (hvξ.trans_lt hlt)]
      · rw [← heq]; exact hy.2 ξ hξ
    have hid : c.σ₀ / y - c.σ₀ / ξ = c.σ₀ * (y - ξ) * (-(y * ξ)⁻¹) := by
      field_simp
      ring
    rw [hw, hid, map_mul, map_mul, Valuation.map_neg, map_inv₀, map_mul, hvξ]
    have hne : v y * v c.σ₀ ≠ 0 := mul_ne_zero hvy.ne' c.vσ_pos.ne'
    calc (1 : Γ₀) = v c.σ₀ * v y * (v y * v c.σ₀)⁻¹ := by rw [mul_comm (v c.σ₀) (v y), mul_inv_cancel₀ hne]
      _ ≤ v c.σ₀ * v (y - ξ) * (v y * v c.σ₀)⁻¹ := mul_le_mul' (mul_le_mul' le_rfl hyξ) le_rfl
  have := hN k hk w ⟨hvw, hwgen⟩ hvw hwgen
  rwa [hWne k w hw0, hyw] at this

theorem main
    (hC : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ y ∈ c.S, v ((c.r k).evalAt y - (c.r j).evalAt y) < v e)
    (h0 : (∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y : K, v y = 1 → (∀ ζ ∈ c.Z, 1 ≤ v (y - ζ)) →
            v ((c.r k).evalAt y) < v e) ∨
          (∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y : K, v y = v c.σ₀ → (∀ ξ ∈ c.Ξ, v c.σ₀ ≤ v (y - ξ)) →
            v ((c.r k).evalAt y) < v e)) :
    ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y : K, c.GoodOut y → c.GoodIn y → v ((c.r k).evalAt y) < v e := by
  obtain ⟨hCout, hCin⟩ := c.cauchy_pieces hC
  have hff : (∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y : K, c.GoodIn y → v (c.fin k y) < v e) ∧
      (∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y : K, c.GoodOut y → v (c.fout k y) < v e) := by
    rcases h0 with h0 | h0
    · obtain ⟨ho, hi1⟩ := c.outer_limits h0
      exact ⟨c.fin_zero hCin hi1, ho⟩
    · obtain ⟨hi, ho1⟩ := c.inner_limits h0
      exact ⟨hi, c.fout_zero hCout ho1⟩
  intro e he
  obtain ⟨N₁, hN₁⟩ := hff.1 e he
  obtain ⟨N₂, hN₂⟩ := hff.2 e he
  refine ⟨max N₁ N₂, fun k hk y hyo hyi => ?_⟩
  rw [c.evalAt_eq k (c.memS hyo hyi)]
  exact Valuation.map_add_lt _ (hN₁ k (le_of_max_le_left hk) y hyi) (hN₂ k (le_of_max_le_right hk) y hyo)

end AData

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

theorem LA0 [IsAlgClosed K] (S : Set K) (r : ℕ → RatPair K) (hpf : ∀ k, (r k).IsPoleFreeOn S)
    (σ₀ : K) (hσ0 : σ₀ ≠ 0) (hσ1 : v σ₀ < 1)
    (Z : Finset K) (hZ : ∀ ζ ∈ Z, 1 ≤ v ζ) (Ξ : Finset K) (hΞ : ∀ ξ ∈ Ξ, v ξ ≤ v σ₀)
    (hS : ∀ y : K, v σ₀ ≤ v y → v y ≤ 1 → (∀ ζ ∈ Z, 1 ≤ v (y - ζ)) → (∀ ξ ∈ Ξ, v σ₀ ≤ v (y - ξ)) → y ∈ S)
    (hC : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ y ∈ S, v ((r k).evalAt y - (r j).evalAt y) < v e)
    (h0 : (∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y : K, v y = 1 → (∀ ζ ∈ Z, 1 ≤ v (y - ζ)) →
            v ((r k).evalAt y) < v e) ∨
          (∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y : K, v y = v σ₀ → (∀ ξ ∈ Ξ, v σ₀ ≤ v (y - ξ)) →
            v ((r k).evalAt y) < v e)) :
    ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y : K, v σ₀ ≤ v y → v y ≤ 1 → (∀ ζ ∈ Z, 1 ≤ v (y - ζ)) →
      (∀ ξ ∈ Ξ, v σ₀ ≤ v (y - ξ)) → v ((r k).evalAt y) < v e := by
  let c : AData K := ⟨S, r, σ₀, Z, Ξ, hpf, hσ0, hσ1, hZ, hΞ, hS⟩
  intro e he
  obtain ⟨N, hN⟩ := c.main hC h0 e he
  exact ⟨N, fun k hk y h1 h2 h3 h4 => hN k hk y ⟨h2, h3⟩ ⟨h1, h4⟩⟩

theorem LA [IsAlgClosed K] (S : Set K) (r : ℕ → RatPair K) (hpf : ∀ k, (r k).IsPoleFreeOn S)
    (c πd πs : K) (hπd : πd ≠ 0) (hπs : πs ≠ 0) (hlt : v πs < v πd)
    (Z : Finset K) (hZ : ∀ ζ ∈ Z, v πd ≤ v (c - ζ))
    (Ξ : Finset K) (hΞ : ∀ ξ ∈ Ξ, v (c - ξ) ≤ v πs)
    (hS : ∀ z : K, v πs ≤ v (z - c) → v (z - c) ≤ v πd → (∀ ζ ∈ Z, v πd ≤ v (z - ζ)) →
      (∀ ξ ∈ Ξ, v πs ≤ v (z - ξ)) → z ∈ S)
    (hC : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ z ∈ S, v ((r k).evalAt z - (r j).evalAt z) < v e)
    (h0 : (∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z : K, v (z - c) = v πd → (∀ ζ ∈ Z, v πd ≤ v (z - ζ)) →
            v ((r k).evalAt z) < v e) ∨
          (∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z : K, v (z - c) = v πs → (∀ ξ ∈ Ξ, v πs ≤ v (z - ξ)) →
            v ((r k).evalAt z) < v e)) :
    ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z : K, v πs ≤ v (z - c) → v (z - c) ≤ v πd →
      (∀ ζ ∈ Z, v πd ≤ v (z - ζ)) → (∀ ξ ∈ Ξ, v πs ≤ v (z - ξ)) → v ((r k).evalAt z) < v e := by
  classical
  have hvd : 0 < v πd := (Valuation.pos_iff _).2 hπd
  have hvs : 0 < v πs := (Valuation.pos_iff _).2 hπs

  let S' : Set K := {y | πd * y + c ∈ S}
  let r' : ℕ → RatPair K := fun k => aff c πd (r k)
  let σ₀ : K := πs / πd
  let Z' : Finset K := Z.image fun ζ => (ζ - c) / πd
  let Ξ' : Finset K := Ξ.image fun ξ => (ξ - c) / πd
  have hσ0 : σ₀ ≠ 0 := div_ne_zero hπs hπd
  have hvσ : v σ₀ = v πs / v πd := map_div₀ _ _ _
  have hσ1 : v σ₀ < 1 := by rw [hvσ, div_lt_iff₀ hvd, one_mul]; exact hlt
  have key_sub : ∀ y t : K, πd * y + c - t = πd * (y - (t - c) / πd) := fun y t => by
    field_simp
    ring

  have dict : ∀ y t : K, v (πd * y + c - t) = v πd * v (y - (t - c) / πd) := fun y t => by
    rw [key_sub, map_mul]
  have dict0 : ∀ y : K, v (πd * y + c - c) = v πd * v y := fun y => by rw [add_sub_cancel_right, map_mul]
  have hpf' : ∀ k, (r' k).IsPoleFreeOn S' := fun k y hy => by
    show (aff c πd (r k)).den.eval y ≠ 0
    rw [aff_den_eval]; exact hpf k _ hy
  have hZ' : ∀ ζ' ∈ Z', 1 ≤ v ζ' := fun ζ' hζ' => by
    obtain ⟨ζ, hζ, rfl⟩ := Finset.mem_image.1 hζ'
    rw [map_div₀, le_div_iff₀ hvd, one_mul, ← neg_sub, Valuation.map_neg]; exact hZ ζ hζ
  have hΞ' : ∀ ξ' ∈ Ξ', v ξ' ≤ v σ₀ := fun ξ' hξ' => by
    obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.1 hξ'
    rw [map_div₀, hvσ, div_le_div_iff_of_pos_right hvd, ← neg_sub, Valuation.map_neg]; exact hΞ ξ hξ

  have cond1 : ∀ y : K, v σ₀ ≤ v y → v πs ≤ v (πd * y + c - c) := fun y h => by
    rw [dict0]; rw [hvσ, div_le_iff₀ hvd, mul_comm] at h; exact h
  have cond2 : ∀ y : K, v y ≤ 1 → v (πd * y + c - c) ≤ v πd := fun y h => by
    rw [dict0]; exact mul_le_of_le_one_right' h
  have cond3 : ∀ y : K, (∀ ζ' ∈ Z', 1 ≤ v (y - ζ')) → ∀ ζ ∈ Z, v πd ≤ v (πd * y + c - ζ) := fun y h ζ hζ => by
    rw [dict]; exact le_mul_of_one_le_right' (h _ (Finset.mem_image_of_mem _ hζ))
  have cond4 : ∀ y : K, (∀ ξ' ∈ Ξ', v σ₀ ≤ v (y - ξ')) → ∀ ξ ∈ Ξ, v πs ≤ v (πd * y + c - ξ) := fun y h ξ hξ => by
    rw [dict]
    have := h _ (Finset.mem_image_of_mem _ hξ)
    rw [hvσ, div_le_iff₀ hvd, mul_comm] at this
    exact this
  have hS'' : ∀ y : K, v σ₀ ≤ v y → v y ≤ 1 → (∀ ζ' ∈ Z', 1 ≤ v (y - ζ')) → (∀ ξ' ∈ Ξ', v σ₀ ≤ v (y - ξ')) →
      y ∈ S' := fun y h1 h2 h3 h4 => hS _ (cond1 y h1) (cond2 y h2) (cond3 y h3) (cond4 y h4)
  have hC' : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ y ∈ S',
      v ((r' k).evalAt y - (r' j).evalAt y) < v e := fun e he => by
    obtain ⟨N, hN⟩ := hC e he
    refine ⟨N, fun k hk j hj y hy => ?_⟩
    show v ((aff c πd (r k)).evalAt y - (aff c πd (r j)).evalAt y) < v e
    rw [aff_evalAt, aff_evalAt]; exact hN k hk j hj _ hy

  have hzy : ∀ z : K, πd * ((z - c) / πd) + c = z := fun z => by field_simp; ring
  have conv1 : ∀ z : K, v (z - c) = v πd → v ((z - c) / πd) = 1 := fun z h => by
    rw [map_div₀, h, div_self hvd.ne']
  have conv1s : ∀ z : K, v (z - c) = v πs → v ((z - c) / πd) = v σ₀ := fun z h => by
    rw [map_div₀, h, hvσ]
  have conv3 : ∀ z : K, (∀ ζ ∈ Z, v πd ≤ v (z - ζ)) → ∀ ζ' ∈ Z', 1 ≤ v ((z - c) / πd - ζ') :=
    fun z h ζ' hζ' => by
    obtain ⟨ζ, hζ, rfl⟩ := Finset.mem_image.1 hζ'
    rw [← sub_div, sub_sub_sub_cancel_right, map_div₀, le_div_iff₀ hvd, one_mul]; exact h ζ hζ
  have conv4 : ∀ z : K, (∀ ξ ∈ Ξ, v πs ≤ v (z - ξ)) → ∀ ξ' ∈ Ξ', v σ₀ ≤ v ((z - c) / πd - ξ') :=
    fun z h ξ' hξ' => by
    obtain ⟨ξ, hξ, rfl⟩ := Finset.mem_image.1 hξ'
    rw [← sub_div, sub_sub_sub_cancel_right, hvσ, map_div₀, div_le_div_iff_of_pos_right hvd]; exact h ξ hξ
  have h0' : (∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y : K, v y = 1 → (∀ ζ' ∈ Z', 1 ≤ v (y - ζ')) →
        v ((r' k).evalAt y) < v e) ∨
      (∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ y : K, v y = v σ₀ → (∀ ξ' ∈ Ξ', v σ₀ ≤ v (y - ξ')) →
        v ((r' k).evalAt y) < v e) := by
    rcases h0 with h0 | h0
    · left
      intro e he
      obtain ⟨N, hN⟩ := h0 e he
      refine ⟨N, fun k hk y hy hyZ => ?_⟩
      show v ((aff c πd (r k)).evalAt y) < v e
      rw [aff_evalAt]
      exact hN k hk _ (by rw [dict0, hy, mul_one]) (cond3 y hyZ)
    · right
      intro e he
      obtain ⟨N, hN⟩ := h0 e he
      refine ⟨N, fun k hk y hy hyΞ => ?_⟩
      show v ((aff c πd (r k)).evalAt y) < v e
      rw [aff_evalAt]
      refine hN k hk _ ?_ (cond4 y hyΞ)
      rw [dict0, hy, hvσ, mul_div_cancel₀ _ hvd.ne']
  have main := LA0 S' r' hpf' σ₀ hσ0 hσ1 Z' hZ' Ξ' hΞ' hS'' hC' h0'
  intro e he
  obtain ⟨N, hN⟩ := main e he
  refine ⟨N, fun k hk z h1 h2 h3 h4 => ?_⟩
  set y := (z - c) / πd with hy
  have hy1 : v σ₀ ≤ v y := by rw [hy, hvσ, map_div₀, div_le_div_iff_of_pos_right hvd]; exact h1
  have hy2 : v y ≤ 1 := by rw [hy, map_div₀, div_le_iff₀ hvd, one_mul]; exact h2
  have := hN k hk y hy1 hy2 (conv3 z h3) (conv4 z h4)
  rwa [show (r' k).evalAt y = (r k).evalAt z from by rw [← hzy z]; exact aff_evalAt c πd (r k) y] at this

end IdAnn

end

open CerednikDrinfeld.Omega in
theorem solution
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (S : Set K) (r : ℕ → RatPair K) (hr : ∀ k, (r k).IsPoleFreeOn S)
    (c πd πs : K) (hπd : πd ≠ 0) (hπs : πs ≠ 0) (hlt : Valued.v πs < Valued.v πd)
    (Z : Finset K) (hZ : ∀ ζ ∈ Z, Valued.v πd ≤ Valued.v (c - ζ))
    (Ξ : Finset K) (hΞ : ∀ ξ ∈ Ξ, Valued.v (c - ξ) ≤ Valued.v πs)
    (hS : ∀ z : K, Valued.v πs ≤ Valued.v (z - c) → Valued.v (z - c) ≤ Valued.v πd →
      (∀ ζ ∈ Z, Valued.v πd ≤ Valued.v (z - ζ)) → (∀ ξ ∈ Ξ, Valued.v πs ≤ Valued.v (z - ξ)) → z ∈ S)
    (hC : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ z ∈ S,
      Valued.v ((r k).evalAt z - (r j).evalAt z) < Valued.v e)
    (h0 : (∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z : K, Valued.v (z - c) = Valued.v πd →
            (∀ ζ ∈ Z, Valued.v πd ≤ Valued.v (z - ζ)) → Valued.v ((r k).evalAt z) < Valued.v e) ∨
          (∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z : K, Valued.v (z - c) = Valued.v πs →
            (∀ ξ ∈ Ξ, Valued.v πs ≤ Valued.v (z - ξ)) → Valued.v ((r k).evalAt z) < Valued.v e)) :
    ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z : K, Valued.v πs ≤ Valued.v (z - c) → Valued.v (z - c) ≤ Valued.v πd →
      (∀ ζ ∈ Z, Valued.v πd ≤ Valued.v (z - ζ)) → (∀ ξ ∈ Ξ, Valued.v πs ≤ Valued.v (z - ξ)) →
      Valued.v ((r k).evalAt z) < Valued.v e :=
  IdAnn.LA S r hr c πd πs hπd hπs hlt Z hZ Ξ hΞ hS hC h0

end S_CerednikDrinfeld_Omega_RatPair_identityPrinciple_annulus
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_RatPair_identityPrinciple_annulus (solution)
