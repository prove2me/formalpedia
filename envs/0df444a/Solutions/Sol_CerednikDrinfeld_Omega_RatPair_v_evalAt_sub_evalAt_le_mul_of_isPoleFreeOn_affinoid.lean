-- Prove2me | solution 1 for CerednikDrinfeld.Omega.RatPair.v_evalAt_sub_evalAt_le_mul_of_isPoleFreeOn_affinoid
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/7c1facc6-bbb3-5fff-9d26-24f0e34cf5e2

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_CerednikDrinfeld_Omega_RatPair_identityPrinciple_disc
import Theorems.Thm_CerednikDrinfeld_Omega_gaussNorm_add_eq_max_of_separated_poles
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_RatPair_v_evalAt_sub_evalAt_le_mul_of_isPoleFreeOn_affinoid

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

section Estimates

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

theorem v_sub_eq_of_lt {x y : K} (h : v y < v x) : v (x - y) = v x := by
  rw [sub_eq_add_neg]
  apply Valuation.map_add_eq_of_lt_left
  rwa [Valuation.map_neg]

theorem sub_eval_le (N : K[X]) {y y₀ : K} (hy : v y ≤ 1) (hy₀ : v y₀ ≤ 1) :
    v (N.eval y - N.eval y₀) ≤ gauss N * v (y - y₀) := by
  have hpow : ∀ i : ℕ, v (y ^ i - y₀ ^ i) ≤ v (y - y₀) := by
    intro i
    rw [← Commute.geom_sum₂_mul (Commute.all y y₀) i, map_mul]
    have hs : v (∑ j ∈ Finset.range i, y ^ j * y₀ ^ (i - 1 - j)) ≤ 1 := by
      refine Valuation.map_sum_le _ fun j _ => ?_
      rw [map_mul, map_pow, map_pow]
      exact mul_le_one' (pow_le_one₀ zero_le' hy) (pow_le_one₀ zero_le' hy₀)
    calc v (∑ j ∈ Finset.range i, y ^ j * y₀ ^ (i - 1 - j)) * v (y - y₀)
        ≤ 1 * v (y - y₀) := mul_le_mul_left hs _
      _ = v (y - y₀) := one_mul _
  have e : N.eval y - N.eval y₀ = ∑ i ∈ N.support, N.coeff i * (y ^ i - y₀ ^ i) := by
    simp only [eval_eq_sum, sum_def, ← Finset.sum_sub_distrib, mul_sub]
  rw [e]
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [map_mul]
  exact mul_le_mul' (v_coeff_le_gauss N i) (hpow i)

variable [IsAlgClosed K]

theorem v_div_le_mul_inv_of_roots_lt_one (N D : K[X]) (hD : D ≠ 0) (hdeg : N.degree < D.degree)
    (hroots : ∀ α ∈ D.roots, v α < 1) {y : K} (hy : 1 ≤ v y) :
    D.eval y ≠ 0 ∧ v (N.eval y / D.eval y) ≤ gauss N / gauss D * (v y)⁻¹ := by
  have hy0 : 0 < v y := zero_lt_one.trans_le hy

  have hlc : gauss D = v D.leadingCoeff := gauss_eq_lc_of_roots D fun α hα => (hroots α hα).le
  have hvD : v (D.eval y) = gauss D * v y ^ D.natDegree := by
    conv_lhs => rw [eq_C_mul_prod D]
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, map_mul, map_multiset_prod, Multiset.map_map, hlc,
      natDegree_eq_card_roots' D]
    congr 1
    have : (Multiset.map ((fun x => v x) ∘ (fun p => eval y p) ∘ fun α => X - C α) D.roots)
        = Multiset.map (fun _ => v y) D.roots := by
      refine Multiset.map_congr rfl fun α hα => ?_
      simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
      exact v_sub_eq_of_lt ((hroots α hα).trans_le hy)
    rw [this, Multiset.map_const', Multiset.prod_replicate]
  have hgD : 0 < gauss D := gauss_pos hD
  have hDy : D.eval y ≠ 0 := by
    rw [← (Valuation.ne_zero_iff Valued.v), hvD]
    exact (mul_pos hgD (pow_pos hy0 _)).ne'
  refine ⟨hDy, ?_⟩
  by_cases hN : N = 0
  · rw [hN, eval_zero, zero_div, map_zero]; exact zero_le'
  have hnd : N.natDegree < D.natDegree := natDegree_lt_natDegree hN hdeg
  obtain ⟨d, hd⟩ : ∃ d : ℕ, D.natDegree = d + 1 := ⟨D.natDegree - 1, by omega⟩
  have hN' : v (N.eval y) ≤ gauss N * v y ^ d :=
    (v_eval_le_gauss_mul_pow N hy).trans (mul_le_mul' le_rfl (pow_le_pow_right₀ hy (by omega)))
  have hvy : v y ≠ 0 := hy0.ne'
  rw [map_div₀, hvD, hd]
  refine (div_le_div_of_nonneg_right hN' zero_le').trans (le_of_eq ?_)
  rw [mul_div_mul_comm, pow_succ, ← div_div, div_self (pow_ne_zero _ hvy), one_div]

theorem v_div_sub_div_le_of_one_lt_roots (N D : K[X]) (hD : D ≠ 0) (hroots : ∀ α ∈ D.roots, 1 < v α)
    {y y₀ : K} (hy : v y ≤ 1) (hy₀ : v y₀ ≤ 1) :
    D.eval y ≠ 0 ∧ D.eval y₀ ≠ 0 ∧
      v (N.eval y / D.eval y - N.eval y₀ / D.eval y₀) ≤ gauss N / gauss D * v (y - y₀) := by
  have hvD : ∀ {u : K}, v u ≤ 1 → v (D.eval u) = gauss D := fun hu =>
    v_eval_eq_gauss D hu fun α hα h1 => absurd (hroots α hα) (not_lt.mpr h1)
  have hgD : 0 < gauss D := gauss_pos hD
  have hDy : D.eval y ≠ 0 := by rw [← (Valuation.ne_zero_iff Valued.v), hvD hy]; exact hgD.ne'
  have hDy₀ : D.eval y₀ ≠ 0 := by rw [← (Valuation.ne_zero_iff Valued.v), hvD hy₀]; exact hgD.ne'
  refine ⟨hDy, hDy₀, ?_⟩
  rw [div_sub_div _ _ hDy hDy₀, map_div₀, map_mul, hvD hy, hvD hy₀]
  have hnum : v (N.eval y * D.eval y₀ - D.eval y * N.eval y₀) ≤ gauss N * v (y - y₀) * gauss D := by
    have e : N.eval y * D.eval y₀ - D.eval y * N.eval y₀
        = (N.eval y - N.eval y₀) * D.eval y₀ - (D.eval y - D.eval y₀) * N.eval y₀ := by ring
    rw [e]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
    · rw [map_mul, hvD hy₀]
      exact mul_le_mul_left (sub_eval_le N hy hy₀) _
    · rw [map_mul]
      calc v (D.eval y - D.eval y₀) * v (N.eval y₀) ≤ (gauss D * v (y - y₀)) * gauss N :=
            mul_le_mul' (sub_eval_le D hy hy₀) (v_eval_le_gauss N hy₀)
        _ = gauss N * v (y - y₀) * gauss D := by ac_rfl
  refine (div_le_div_of_nonneg_right hnum zero_le').trans (le_of_eq ?_)
  rw [mul_div_mul_right _ _ hgD.ne', mul_div_right_comm]

end Estimates

end IdAnn

namespace RatOsc

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] (ϖ : PseudoUniformizer K₀ K)

theorem v_sub_eq_left {x y : K} (h : Valued.v y < Valued.v x) : Valued.v (x - y) = Valued.v x := by
  rw [sub_eq_add_neg]
  apply Valuation.map_add_eq_of_lt_left
  rwa [Valuation.map_neg]

theorem v_sub_eq_right {x y : K} (h : Valued.v x < Valued.v y) : Valued.v (x - y) = Valued.v y := by
  rw [Valuation.map_sub_swap]; exact v_sub_eq_left h

theorem v_sub_comm (x y : K) : Valued.v (x - y) = Valued.v (y - x) := Valuation.map_sub_swap _ x y

theorem p_pow_le_one (m : ℕ) : Valued.v (algebraMap K₀ K ϖ.ϖ) ^ m ≤ 1 := pow_le_one₀ zero_le' ϖ.lt_one.le

theorem one_le_P_pow (m : ℕ) : 1 ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m :=
  one_le_pow₀ ((one_le_inv₀ ϖ.pos).2 ϖ.lt_one.le)

theorem p_pow_le_P_pow (m : ℕ) :
    Valued.v (algebraMap K₀ K ϖ.ϖ) ^ m ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m :=
  (p_pow_le_one ϖ m).trans (one_le_P_pow ϖ m)

theorem mem_affinoid_of_v_sub_eq (m : ℕ) (T : Finset K₀)
    (hT : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ m)
    (t : K₀) (ht : Valued.v (algebraMap K₀ K t) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m) (z : K)
    (hz : Valued.v (z - algebraMap K₀ K t) = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ m)
    (hgen : ∀ s ∈ T, Valued.v (algebraMap K₀ K s - algebraMap K₀ K t) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ m →
      Valued.v (algebraMap K₀ K ϖ.ϖ) ^ m ≤ Valued.v (z - algebraMap K₀ K s)) :
    z ∈ affinoid ϖ m := by
  rw [mem_affinoid_iff']
  refine ⟨?_, fun a => ?_⟩
  ·
    have e : z = (z - algebraMap K₀ K t) + algebraMap K₀ K t := by ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ht)
    rw [hz]; exact p_pow_le_P_pow ϖ m
  ·
    have key : z - algebraMap K₀ K a = (z - algebraMap K₀ K t) - (algebraMap K₀ K a - algebraMap K₀ K t) := by ring
    rcases lt_trichotomy (Valued.v (algebraMap K₀ K a - algebraMap K₀ K t)) (Valued.v (algebraMap K₀ K ϖ.ϖ) ^ m)
      with hlt | heq | hgt
    ·
      rw [key, v_sub_eq_left (by rw [hz]; exact hlt), hz]
    ·
      have ha : Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m := by
        have e : algebraMap K₀ K a = (algebraMap K₀ K a - algebraMap K₀ K t) + algebraMap K₀ K t := by ring
        rw [e]
        refine (Valuation.map_add _ _ _).trans (max_le ?_ ht)
        rw [heq]; exact p_pow_le_P_pow ϖ m
      obtain ⟨s, hsT, hs⟩ := hT a ha
      have hst : Valued.v (algebraMap K₀ K s - algebraMap K₀ K t) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ m := by
        have e : algebraMap K₀ K s - algebraMap K₀ K t
            = (algebraMap K₀ K a - algebraMap K₀ K t) - (algebraMap K₀ K a - algebraMap K₀ K s) := by ring
        rw [e]
        refine (Valuation.map_sub _ _ _).trans (max_le heq.le hs.le)
      have hzs := hgen s hsT hst

      have e2 : z - algebraMap K₀ K a = (z - algebraMap K₀ K s) - (algebraMap K₀ K a - algebraMap K₀ K s) := by ring
      rw [e2, v_sub_eq_left (hs.trans_le hzs)]
      exact hzs
    ·
      rw [key, v_sub_eq_right (by rw [hz]; exact hgt)]
      exact hgt.le

theorem mem_affinoid_of_v_eq (m : ℕ) (T : Finset K₀)
    (hT : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ m)
    (z : K) (hz : Valued.v z = (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m)
    (hgen : ∀ s ∈ T, Valued.v (algebraMap K₀ K s) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m →
      (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m ≤ Valued.v (z - algebraMap K₀ K s)) :
    z ∈ affinoid ϖ m := by
  refine ⟨hz.le, fun a ha => ?_⟩

  rcases lt_or_eq_of_le ha with hlt | heq
  · rw [v_sub_eq_left (by rw [hz]; exact hlt), hz]; exact p_pow_le_P_pow ϖ m
  · obtain ⟨s, hsT, hs⟩ := hT a ha
    have hsz : Valued.v (algebraMap K₀ K s) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m := by
      have e : algebraMap K₀ K s = algebraMap K₀ K a - (algebraMap K₀ K a - algebraMap K₀ K s) := by ring
      rw [e]
      refine (Valuation.map_sub _ _ _).trans (max_le ha (hs.le.trans (p_pow_le_P_pow ϖ m)))
    have hzs := hgen s hsT hsz
    have e2 : z - algebraMap K₀ K a = (z - algebraMap K₀ K s) - (algebraMap K₀ K a - algebraMap K₀ K s) := by ring
    rw [e2, v_sub_eq_left (hs.trans_le ((p_pow_le_P_pow ϖ m).trans hzs))]
    exact (p_pow_le_P_pow ϖ m).trans hzs

theorem exists_v_sub_lt_of_not_mem_affinoid (m : ℕ) {α : K}
    (hα : Valued.v α ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m) (hαn : α ∉ affinoid ϖ m) :
    ∃ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m ∧
      Valued.v (α - algebraMap K₀ K a) < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ m := by
  simp only [affinoid, Set.mem_setOf_eq, not_and, not_forall, not_le] at hαn
  obtain ⟨a, ha, hlt⟩ := hαn hα
  exact ⟨a, ha, hlt⟩

theorem p_pow_le_v_sub_of_mem_affinoid (n : ℕ) {z : K} (hz : z ∈ affinoid ϖ n) (a : K₀) :
    Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n ≤ Valued.v (z - algebraMap K₀ K a) :=
  ((mem_affinoid_iff' ϖ n z).1 hz).2 a

theorem mem_affinoid_of_le {n m : ℕ} (hnm : n ≤ m) {z : K} (hz : z ∈ affinoid ϖ n) : z ∈ affinoid ϖ m :=
  affinoid_mono ϖ hnm hz

theorem v_le_of_mem_affinoid (n : ℕ) {z : K} (hz : z ∈ affinoid ϖ n) :
    Valued.v z ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n := hz.1

end RatOsc

namespace RatOsc

open IdAnn Polynomial

section Bounds

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K] (ϖ : PseudoUniformizer K₀ K)

omit [IsAlgClosed K] in
theorem eval_comp_affine (P : K[X]) (π c y : K) : (P.comp (C π * X + C c)).eval y = P.eval (π * y + c) := by
  rw [eval_comp, eval_add, eval_mul, eval_C, eval_X, eval_C]

theorem gauss_le_of_split (m : ℕ) (T : Finset K₀)
    (hT : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ m)
    (t : K₀) (ht : Valued.v (algebraMap K₀ K t) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m)
    (r : RatPair K) (hr : r.IsPoleFreeOn (affinoid ϖ m)) (b : K)
    (hb : ∀ w : K, w ∈ affinoid ϖ m → Valued.v (r.evalAt w) ≤ Valued.v b)
    (NA DA NB DB : K[X]) (hDA : DA ≠ 0) (hDB : DB ≠ 0) (hdeg : NA.degree < DA.degree)
    (hA : ∀ α ∈ DA.roots, Valued.v α < 1) (hB : ∀ β ∈ DB.roots, 1 ≤ Valued.v β)
    (hnum : NA * DB + NB * DA = r.num.comp (C ((algebraMap K₀ K ϖ.ϖ) ^ m) * X + C (algebraMap K₀ K t)))
    (hden : DA * DB = r.den.comp (C ((algebraMap K₀ K ϖ.ϖ) ^ m) * X + C (algebraMap K₀ K t))) :
    gauss NA ≤ Valued.v b * gauss DA ∧ gauss NB ≤ Valued.v b * gauss DB := by
  classical
  set π : K := (algebraMap K₀ K ϖ.ϖ) ^ m with hπ
  set tK : K := algebraMap K₀ K t with htK
  have hvπ : Valued.v π = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ m := by rw [hπ, map_pow]
  have hπpos : 0 < Valued.v π := by rw [hvπ]; exact pow_pos ϖ.pos _
  have hπ0 : π ≠ 0 := (Valuation.ne_zero_iff Valued.v).mp hπpos.ne'
  let Bad : Multiset K := T.val.map fun s => (algebraMap K₀ K s - tK) / π

  have hval : ∀ y : K, Valued.v y = 1 → (∀ b' ∈ Bad, Valued.v b' ≤ 1 → 1 ≤ Valued.v (y - b')) →
      Valued.v ((NA * DB + NB * DA).eval y / (DA.eval y * DB.eval y)) ≤ Valued.v b := by
    intro y hy hgenB
    set z : K := π * y + tK with hz
    have hzt : Valued.v (z - tK) = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ m := by
      rw [hz, add_sub_cancel_right, map_mul, hy, mul_one, hvπ]
    have hgen : ∀ s ∈ T, Valued.v (algebraMap K₀ K s - algebraMap K₀ K t) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ m →
        Valued.v (algebraMap K₀ K ϖ.ϖ) ^ m ≤ Valued.v (z - algebraMap K₀ K s) := by
      intro s hs hst
      have hmem : (algebraMap K₀ K s - tK) / π ∈ Bad := Multiset.mem_map_of_mem _ (Finset.mem_val.mpr hs)
      have hle : Valued.v ((algebraMap K₀ K s - tK) / π) ≤ 1 := by
        rw [map_div₀, div_le_iff₀ hπpos, one_mul, hvπ]; exact hst
      have h1 := hgenB _ hmem hle
      have e : z - algebraMap K₀ K s = π * (y - (algebraMap K₀ K s - tK) / π) := by
        rw [hz, mul_sub, mul_div_cancel₀ _ hπ0]; ring
      rw [e, map_mul, hvπ]
      exact le_mul_of_one_le_right' h1
    have hzmem : z ∈ affinoid ϖ m := mem_affinoid_of_v_sub_eq ϖ m T hT t ht z hzt hgen
    have hval' : (NA * DB + NB * DA).eval y / (DA.eval y * DB.eval y) = r.evalAt z := by
      rw [← eval_mul, hnum, hden, eval_comp_affine, eval_comp_affine, RatPair.evalAt]
    rw [hval']
    exact hb z hzmem
  have hgDA : 0 < gauss DA := gauss_pos hDA
  have hgDB : 0 < gauss DB := gauss_pos hDB
  constructor
  · by_contra h
    rw [not_le] at h
    have hε : Valued.v b < gauss NA / gauss DA := by rw [lt_div_iff₀ hgDA]; exact h
    have := (core_outer NA DA NB DB hDA hDB hdeg hA hB Bad (ε := gauss NA / gauss DA)
      (fun y hy hg => (hval y hy hg).trans_lt hε)).1
    rw [div_mul_cancel₀ _ hgDA.ne'] at this
    exact lt_irrefl _ this
  · by_contra h
    rw [not_le] at h
    have hε : Valued.v b < gauss NB / gauss DB := by rw [lt_div_iff₀ hgDB]; exact h
    have := (core_outer NA DA NB DB hDA hDB hdeg hA hB Bad (ε := gauss NB / gauss DB)
      (fun y hy hg => (hval y hy hg).trans_lt hε)).2
    rw [div_mul_cancel₀ _ hgDB.ne'] at this
    exact lt_irrefl _ this

theorem lt_roots_comp_outer (m : ℕ) (r : RatPair K) (hr0 : r.den ≠ 0)
    (hroots : ∀ α ∈ r.den.roots, (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m < Valued.v α) :
    ∀ β ∈ (r.den.comp (C ((algebraMap K₀ K ϖ.ϖ)⁻¹ ^ m) * X)).roots, 1 < Valued.v β := by
  intro β hβ
  set πi : K := (algebraMap K₀ K ϖ.ϖ)⁻¹ ^ m with hπi
  have hvπi : Valued.v πi = (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m := by rw [hπi, map_pow, map_inv₀]
  have hπipos : 0 < Valued.v πi := by
    rw [hvπi]; exact pow_pos (inv_pos.mpr ϖ.pos) _
  have hπi0 : πi ≠ 0 := (Valuation.ne_zero_iff Valued.v).mp hπipos.ne'
  have hmem := roots_comp_C_mul_X hr0 hπi0 hβ
  have h := hroots _ hmem
  rw [map_mul, hvπi] at h
  have h' : (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m * 1 < (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m * Valued.v β := by
    rwa [mul_one]
  exact lt_of_mul_lt_mul_left' h'

theorem gauss_le_of_forall_lt_roots (m : ℕ) (T : Finset K₀)
    (hT : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ m)
    (r : RatPair K) (hr0 : r.den ≠ 0)
    (hr : r.IsPoleFreeOn (affinoid ϖ m)) (b : K)
    (hb : ∀ w : K, w ∈ affinoid ϖ m → Valued.v (r.evalAt w) ≤ Valued.v b)
    (hroots : ∀ α ∈ r.den.roots, (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m < Valued.v α) :
    gauss (r.num.comp (C ((algebraMap K₀ K ϖ.ϖ)⁻¹ ^ m) * X)) ≤
      Valued.v b * gauss (r.den.comp (C ((algebraMap K₀ K ϖ.ϖ)⁻¹ ^ m) * X)) := by
  classical
  set πi : K := (algebraMap K₀ K ϖ.ϖ)⁻¹ ^ m with hπi
  set Nt : K[X] := r.num.comp (C πi * X) with hNt
  set Dt : K[X] := r.den.comp (C πi * X) with hDt
  have hvπi : Valued.v πi = (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m := by rw [hπi, map_pow, map_inv₀]
  have hπipos : 0 < Valued.v πi := by rw [hvπi]; exact pow_pos (inv_pos.mpr ϖ.pos) _
  have hπi0 : πi ≠ 0 := (Valuation.ne_zero_iff Valued.v).mp hπipos.ne'
  have hDt0 : Dt ≠ 0 := by
    rw [hDt, Ne, comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_of_ne_zero hπi0)]; exact hr0
  have hDtroots : ∀ β ∈ Dt.roots, 1 < Valued.v β := lt_roots_comp_outer ϖ m r hr0 hroots

  obtain ⟨y, hy1, hygen⟩ := exists_generic ((0 : K) ::ₘ (Nt.roots + T.val.map fun s => (algebraMap K₀ K ϖ.ϖ) ^ m * algebraMap K₀ K s))
  have hy : Valued.v y = 1 :=
    le_antisymm hy1 (by simpa using hygen 0 (Multiset.mem_cons_self _ _) (by simp))
  set z : K := πi * y with hz
  have hvz : Valued.v z = (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m := by rw [hz, map_mul, hy, mul_one, hvπi]
  have hππ : πi * (algebraMap K₀ K ϖ.ϖ) ^ m = 1 := by
    rw [hπi, ← mul_pow, inv_mul_cancel₀ ((Valuation.ne_zero_iff Valued.v).mp ϖ.pos.ne'), one_pow]
  have hgen : ∀ s ∈ T, Valued.v (algebraMap K₀ K s) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m →
      (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m ≤ Valued.v (z - algebraMap K₀ K s) := by
    intro s hs hsv
    have hmem : (algebraMap K₀ K ϖ.ϖ) ^ m * algebraMap K₀ K s ∈
        (0 : K) ::ₘ (Nt.roots + T.val.map fun s => (algebraMap K₀ K ϖ.ϖ) ^ m * algebraMap K₀ K s) :=
      Multiset.mem_cons_of_mem (Multiset.mem_add.mpr (Or.inr (Multiset.mem_map_of_mem _ (Finset.mem_val.mpr hs))))
    have hle : Valued.v ((algebraMap K₀ K ϖ.ϖ) ^ m * algebraMap K₀ K s) ≤ 1 := by
      rw [map_mul, map_pow]
      calc Valued.v (algebraMap K₀ K ϖ.ϖ) ^ m * Valued.v (algebraMap K₀ K s)
          ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ m * (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m := mul_le_mul' le_rfl hsv
        _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ ϖ.pos.ne', one_pow]
    have h1 := hygen _ hmem hle
    have e : z - algebraMap K₀ K s = πi * (y - (algebraMap K₀ K ϖ.ϖ) ^ m * algebraMap K₀ K s) := by
      rw [mul_sub, ← mul_assoc, hππ, one_mul, hz]
    rw [e, map_mul, hvπi]
    exact le_mul_of_one_le_right' h1
  have hzmem : z ∈ affinoid ϖ m := mem_affinoid_of_v_eq ϖ m T hT z hvz hgen
  have hden : r.den.eval z ≠ 0 := hr z hzmem
  have hbz := hb z hzmem

  have hvD : Valued.v (Dt.eval y) = gauss Dt :=
    v_eval_eq_gauss Dt hy1 fun β hβ h1 => absurd (hDtroots β hβ) (not_lt.mpr h1)
  have hgDt : 0 < gauss Dt := gauss_pos hDt0
  have hNe : Nt.eval y = r.num.eval z := by rw [hNt, eval_comp_C_mul_X, hz]
  have hDe : Dt.eval y = r.den.eval z := by rw [hDt, eval_comp_C_mul_X, hz]
  by_cases hNt0 : Nt = 0
  · rw [hNt0, gauss_zero]; exact zero_le'
  have hvN : Valued.v (Nt.eval y) = gauss Nt :=
    v_eval_eq_gauss Nt hy1 fun α hα h1 =>
      hygen α (Multiset.mem_cons_of_mem (Multiset.mem_add.mpr (Or.inl hα))) h1
  show gauss Nt ≤ Valued.v b * gauss Dt
  rw [← hvN, ← hvD, ← div_le_iff₀ (by rw [hvD]; exact hgDt), ← map_div₀, hNe, hDe]
  exact hbz

end Bounds

end RatOsc

namespace IdAnn

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

local notation "v" => (Valued.v (R := K) (Γ₀ := Γ₀))

section SplitP

variable [IsAlgClosed K] (p : K → Prop)

open scoped Classical

def inRootsP (Q : K[X]) : Multiset K := Q.roots.filter p

def outRootsP (Q : K[X]) : Multiset K := Q.roots.filter fun α => ¬ p α

def QinP (Q : K[X]) : K[X] := ((inRootsP p Q).map fun α => X - C α).prod

def QoutP (Q : K[X]) : K[X] := C Q.leadingCoeff * ((outRootsP p Q).map fun α => X - C α).prod

omit [IsAlgClosed K] in
theorem QinP_monic (Q : K[X]) : (QinP p Q).Monic := monic_multiset_prod_of_monic _ _ fun α _ => monic_X_sub_C α

omit [IsAlgClosed K] in
theorem QinP_ne_zero (Q : K[X]) : QinP p Q ≠ 0 := (QinP_monic p Q).ne_zero

theorem QinP_mul_QoutP (Q : K[X]) : QinP p Q * QoutP p Q = Q := by
  rw [QinP, QoutP, mul_left_comm, ← Multiset.prod_add, ← Multiset.map_add, inRootsP, outRootsP,
    Multiset.filter_add_not]
  exact (eq_C_mul_prod Q).symm

theorem QoutP_ne_zero {Q : K[X]} (hQ : Q ≠ 0) : QoutP p Q ≠ 0 := fun h => hQ (by rw [← QinP_mul_QoutP p Q, h, mul_zero])

omit [IsAlgClosed K] in
theorem roots_QinP (Q : K[X]) : (QinP p Q).roots = inRootsP p Q := roots_multiset_prod_X_sub_C _

omit [IsAlgClosed K] in
theorem mem_roots_QinP {Q : K[X]} {α : K} : α ∈ (QinP p Q).roots ↔ α ∈ Q.roots ∧ p α := by
  rw [roots_QinP, inRootsP, Multiset.mem_filter]

omit [IsAlgClosed K] in
theorem roots_QoutP {Q : K[X]} (hQ : Q ≠ 0) : (QoutP p Q).roots = outRootsP p Q := by
  rw [QoutP, roots_C_mul _ (leadingCoeff_ne_zero.2 hQ), roots_multiset_prod_X_sub_C]

omit [IsAlgClosed K] in
theorem mem_roots_QoutP {Q : K[X]} (hQ : Q ≠ 0) {α : K} : α ∈ (QoutP p Q).roots ↔ α ∈ Q.roots ∧ ¬ p α := by
  rw [roots_QoutP p hQ, outRootsP, Multiset.mem_filter]

omit [IsAlgClosed K] in
theorem natDegree_QinP (Q : K[X]) : (QinP p Q).natDegree = Multiset.card (inRootsP p Q) := by
  rw [QinP, natDegree_multiset_prod_X_sub_C_eq_card]

theorem isCoprime_QinP_QoutP (Q : K[X]) : IsCoprime (QinP p Q) (QoutP p Q) := by
  rw [isCoprime_iff_aeval_ne_zero_of_isAlgClosed K K]
  intro a
  simp only [coe_aeval_eq_eval]
  by_cases hQ : Q = 0
  · left
    have : inRootsP p Q = 0 := by rw [inRootsP, hQ, roots_zero, Multiset.filter_zero]
    rw [QinP, this, Multiset.map_zero, Multiset.prod_zero, eval_one]; exact one_ne_zero
  by_cases ha : p a
  · right
    intro h
    have hmem : a ∈ (QoutP p Q).roots := (mem_roots (QoutP_ne_zero p hQ)).2 h
    exact ((mem_roots_QoutP p hQ).1 hmem).2 ha
  · left
    intro h
    have hmem : a ∈ (QinP p Q).roots := (mem_roots (QinP_ne_zero p Q)).2 h
    exact ha ((mem_roots_QinP p).1 hmem).2

def bezAP (Q : K[X]) : K[X] := Classical.choose (isCoprime_QinP_QoutP p Q)

def bezBP (Q : K[X]) : K[X] := Classical.choose (Classical.choose_spec (isCoprime_QinP_QoutP p Q))

theorem bezP_spec (Q : K[X]) : bezAP p Q * QinP p Q + bezBP p Q * QoutP p Q = 1 :=
  Classical.choose_spec (Classical.choose_spec (isCoprime_QinP_QoutP p Q))

def inNumP (P Q : K[X]) : K[X] := (P * bezBP p Q) %ₘ QinP p Q

def outNumP (P Q : K[X]) : K[X] := (P * bezBP p Q) /ₘ QinP p Q * QoutP p Q + P * bezAP p Q

theorem split_eqP (P Q : K[X]) : inNumP p P Q * QoutP p Q + outNumP p P Q * QinP p Q = P := by
  have h1 := modByMonic_add_div (P * bezBP p Q) (QinP p Q)
  have h2 := bezP_spec p Q
  rw [outNumP, add_mul, inNumP]
  calc (P * bezBP p Q) %ₘ QinP p Q * QoutP p Q +
          ((P * bezBP p Q) /ₘ QinP p Q * QoutP p Q * QinP p Q + P * bezAP p Q * QinP p Q)
        = ((P * bezBP p Q) %ₘ QinP p Q + QinP p Q * ((P * bezBP p Q) /ₘ QinP p Q)) * QoutP p Q +
            P * bezAP p Q * QinP p Q := by
          ring
    _ = P * (bezAP p Q * QinP p Q + bezBP p Q * QoutP p Q) := by rw [h1]; ring
    _ = P := by rw [h2, mul_one]

theorem degree_inNumP_lt (P Q : K[X]) : (inNumP p P Q).degree < (QinP p Q).degree :=
  degree_modByMonic_lt _ (QinP_monic p Q)

theorem natDegree_inNumP_le (P Q : K[X]) : (inNumP p P Q).natDegree ≤ (QinP p Q).natDegree := by
  by_cases h : inNumP p P Q = 0
  · rw [h, natDegree_zero]; exact Nat.zero_le _
  · exact (natDegree_lt_natDegree h (degree_inNumP_lt p P Q)).le

theorem eval_splitP (P Q : K[X]) {y : K} (hy : Q.eval y ≠ 0) :
    (QinP p Q).eval y ≠ 0 ∧ (QoutP p Q).eval y ≠ 0 ∧
      P.eval y / Q.eval y = (inNumP p P Q).eval y / (QinP p Q).eval y + (outNumP p P Q).eval y / (QoutP p Q).eval y := by
  have hQ : Q.eval y = (QinP p Q).eval y * (QoutP p Q).eval y := by rw [← eval_mul, QinP_mul_QoutP]
  rw [hQ] at hy
  have h1 : (QinP p Q).eval y ≠ 0 := left_ne_zero_of_mul hy
  have h2 : (QoutP p Q).eval y ≠ 0 := right_ne_zero_of_mul hy
  refine ⟨h1, h2, ?_⟩
  rw [div_add_div _ _ h1 h2, hQ]
  congr 1
  conv_lhs => rw [← split_eqP p P Q]
  simp only [eval_add, eval_mul]
  ring

theorem roots_QinP_add_roots_QoutP {Q : K[X]} (hQ : Q ≠ 0) : (QinP p Q).roots + (QoutP p Q).roots = Q.roots := by
  rw [roots_QinP, roots_QoutP p hQ, inRootsP, outRootsP, Multiset.filter_add_not]

omit [IsAlgClosed K] in

theorem card_filter_roots_QoutP' [IsAlgClosed K] {Q : K[X]} (hQ : Q ≠ 0) (q : K → Prop) [DecidablePred q] :
    ((QoutP p Q).roots.filter q).card + ((QinP p Q).roots.filter q).card = (Q.roots.filter q).card := by
  rw [← roots_QinP_add_roots_QoutP p hQ, Multiset.filter_add, Multiset.card_add, add_comm]

theorem card_filter_roots_QoutP {Q : K[X]} (hQ : Q ≠ 0) (q : K → Prop) :
    ((QoutP p Q).roots.filter q).card + ((QinP p Q).roots.filter q).card = (Q.roots.filter q).card := by
  rw [← roots_QinP_add_roots_QoutP p hQ, Multiset.filter_add, Multiset.card_add, add_comm]

end SplitP

section Affine

theorem eval_comp_lin (P : K[X]) (π c y : K) : (P.comp (C π * X + C c)).eval y = P.eval (π * y + c) := by
  rw [eval_comp, eval_add, eval_mul, eval_C, eval_X, eval_C]

theorem natDegree_lin {π : K} (hπ : π ≠ 0) (c : K) : (C π * X + C c : K[X]).natDegree = 1 := by
  rw [natDegree_add_C, natDegree_C_mul_X π hπ]

theorem lin_ne_zero {π : K} (hπ : π ≠ 0) (c : K) : (C π * X + C c : K[X]) ≠ 0 := by
  intro h
  have := natDegree_lin hπ c
  rw [h, natDegree_zero] at this
  exact zero_ne_one this

theorem natDegree_comp_lin (P : K[X]) {π : K} (hπ : π ≠ 0) (c : K) :
    (P.comp (C π * X + C c)).natDegree = P.natDegree := by
  rw [natDegree_comp, natDegree_lin hπ c, mul_one]

theorem comp_lin_ne_zero {P : K[X]} (hP : P ≠ 0) {π : K} (hπ : π ≠ 0) (c : K) : P.comp (C π * X + C c) ≠ 0 := by
  intro h
  by_cases hdeg : P.natDegree = 0
  ·
    obtain ⟨a, rfl⟩ : ∃ a, P = C a := ⟨P.coeff 0, eq_C_of_natDegree_eq_zero hdeg⟩
    rw [C_comp] at h
    exact hP h
  · have := natDegree_comp_lin P hπ c
    rw [h, natDegree_zero] at this
    exact hdeg this.symm

theorem degree_comp_lin (P : K[X]) {π : K} (hπ : π ≠ 0) (c : K) :
    (P.comp (C π * X + C c)).degree = P.degree := by
  by_cases hP : P = 0
  · rw [hP, zero_comp]
  · rw [degree_eq_natDegree (comp_lin_ne_zero hP hπ c), degree_eq_natDegree hP, natDegree_comp_lin P hπ c]

theorem mem_roots_of_mem_roots_comp_lin {P : K[X]} (hP : P ≠ 0) {π : K} (hπ : π ≠ 0) (c : K) {β : K}
    (h : β ∈ (P.comp (C π * X + C c)).roots) : π * β + c ∈ P.roots := by
  have := (mem_roots (comp_lin_ne_zero hP hπ c)).1 h
  rw [IsRoot.def, eval_comp_lin] at this
  exact (mem_roots hP).2 this

theorem mem_roots_comp_lin_of_mem_roots {P : K[X]} (hP : P ≠ 0) {π : K} (hπ : π ≠ 0) (c : K) {α : K}
    (h : α ∈ P.roots) : (α - c) / π ∈ (P.comp (C π * X + C c)).roots := by
  rw [mem_roots (comp_lin_ne_zero hP hπ c), IsRoot.def, eval_comp_lin, mul_div_cancel₀ _ hπ, sub_add_cancel]
  exact (mem_roots hP).1 h

end Affine

end IdAnn

namespace RatOsc

open IdAnn Polynomial

section Peel

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K] (ϖ : PseudoUniformizer K₀ K)

theorem peel_step (m n : ℕ) (hnm : n ≤ m) (T : Finset K₀)
    (hT : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ m)
    (b : K) (r : RatPair K) (hr0 : r.den ≠ 0) (hr : r.IsPoleFreeOn (affinoid ϖ m))
    (hb : ∀ w : K, w ∈ affinoid ϖ m → Valued.v (r.evalAt w) ≤ Valued.v b)
    (α₀ : K) (hα₀ : α₀ ∈ r.den.roots) (hα₀D : Valued.v α₀ ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m) :
    ∃ r' : RatPair K, r'.den ≠ 0 ∧ r'.IsPoleFreeOn (affinoid ϖ m) ∧
      (∀ w : K, w ∈ affinoid ϖ m → Valued.v (r'.evalAt w) ≤ Valued.v b) ∧
      (r'.den.roots.filter (fun α => Valued.v α ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m)).card <
        (r.den.roots.filter (fun α => Valued.v α ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m)).card ∧
      ∀ z z₀ : K, z ∈ affinoid ϖ n → z₀ ∈ affinoid ϖ n →
        Valued.v (r.evalAt z - r.evalAt z₀) ≤
          max (Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (m - n) * Valued.v b) (Valued.v (r'.evalAt z - r'.evalAt z₀)) := by
  classical

  set ϖK : K := algebraMap K₀ K ϖ.ϖ with hϖK
  set 𝔭 : Γ₀ := Valued.v ϖK with h𝔭
  have h𝔭0 : 𝔭 ≠ 0 := ϖ.pos.ne'
  have h𝔭pos : 0 < 𝔭 := ϖ.pos
  have hϖK0 : ϖK ≠ 0 := (Valuation.ne_zero_iff Valued.v).mp h𝔭0
  set π : K := ϖK ^ m with hπ
  have hπ0 : π ≠ 0 := pow_ne_zero _ hϖK0
  have hvπ : Valued.v π = 𝔭 ^ m := by rw [hπ, map_pow]
  have hπpos : 0 < 𝔭 ^ m := pow_pos h𝔭pos m

  have hα₀n : α₀ ∉ affinoid ϖ m := by
    intro hmem
    exact hr α₀ hmem (((mem_roots hr0).1 hα₀).eq_zero)
  obtain ⟨a, ha, hαa⟩ := exists_v_sub_lt_of_not_mem_affinoid ϖ m hα₀D hα₀n
  set t : K := algebraMap K₀ K a with ht

  set p : K → Prop := fun α => Valued.v (α - t) < 𝔭 ^ m with hp
  set Qi := QinP p r.den with hQi
  set Qo := QoutP p r.den with hQo
  set Ni := inNumP p r.num r.den with hNi
  set No := outNumP p r.num r.den with hNo

  set L : K[X] := C π * X + C t with hL
  have hDA : Qi.comp L ≠ 0 := comp_lin_ne_zero (QinP_ne_zero p r.den) hπ0 t
  have hDB : Qo.comp L ≠ 0 := comp_lin_ne_zero (QoutP_ne_zero p hr0) hπ0 t
  have hdeg : (Ni.comp L).degree < (Qi.comp L).degree := by
    rw [degree_comp_lin _ hπ0, degree_comp_lin _ hπ0]; exact degree_inNumP_lt p r.num r.den
  have hA : ∀ β ∈ (Qi.comp L).roots, Valued.v β < 1 := by
    intro β hβ
    have h1 := mem_roots_of_mem_roots_comp_lin (QinP_ne_zero p r.den) hπ0 t hβ
    have h2 : p (π * β + t) := ((mem_roots_QinP p).1 h1).2
    simp only [hp, add_sub_cancel_right, map_mul, hvπ] at h2
    by_contra hge
    rw [not_lt] at hge
    have : 𝔭 ^ m * 1 ≤ 𝔭 ^ m * Valued.v β := mul_le_mul_right hge _
    rw [mul_one] at this
    exact absurd (lt_of_le_of_lt this h2) (lt_irrefl _)
  have hB : ∀ β ∈ (Qo.comp L).roots, 1 ≤ Valued.v β := by
    intro β hβ
    have h1 := mem_roots_of_mem_roots_comp_lin (QoutP_ne_zero p hr0) hπ0 t hβ
    have h2 : ¬ p (π * β + t) := ((mem_roots_QoutP p hr0).1 h1).2
    simp only [hp, add_sub_cancel_right, map_mul, hvπ, not_lt] at h2
    exact (le_mul_iff_one_le_right hπpos).mp h2
  have hnum : Ni.comp L * Qo.comp L + No.comp L * Qi.comp L = r.num.comp (C (ϖK ^ m) * X + C t) := by
    rw [← mul_comp, ← mul_comp, ← add_comp, hNi, hNo, hQi, hQo, split_eqP]
  have hden : Qi.comp L * Qo.comp L = r.den.comp (C (ϖK ^ m) * X + C t) := by
    rw [← mul_comp, hQi, hQo, QinP_mul_QoutP]
  obtain ⟨hgA, -⟩ := gauss_le_of_split ϖ m T hT a ha r hr b hb (Ni.comp L) (Qi.comp L) (No.comp L) (Qo.comp L)
    hDA hDB hdeg hA hB hnum hden
  have hgauss : gauss (Ni.comp L) / gauss (Qi.comp L) ≤ Valued.v b := by
    rw [div_le_iff₀ (gauss_pos hDA)]; exact hgA

  have est : ∀ (w : K) (k : ℕ), k ≤ m → 𝔭 ^ k ≤ Valued.v (w - t) →
      Qi.eval w ≠ 0 ∧ Valued.v (Ni.eval w / Qi.eval w) ≤ 𝔭 ^ (m - k) * Valued.v b := by
    intro w k hkm hwk
    have hkm' : 𝔭 ^ m ≤ 𝔭 ^ k := pow_le_pow_right_of_le_one' ϖ.lt_one.le hkm
    have hwpos : 0 < Valued.v (w - t) := lt_of_lt_of_le (pow_pos h𝔭pos k) hwk
    set y : K := (w - t) / π with hy
    have hyw : π * y + t = w := by rw [hy, mul_div_cancel₀ _ hπ0, sub_add_cancel]
    have hvy : Valued.v y = Valued.v (w - t) / 𝔭 ^ m := by rw [hy, map_div₀, hvπ]
    have hy1 : 1 ≤ Valued.v y := by
      rw [hvy, le_div_iff₀ hπpos, one_mul]; exact hkm'.trans hwk
    obtain ⟨hD0, hE⟩ := v_div_le_mul_inv_of_roots_lt_one (Ni.comp L) (Qi.comp L) hDA hdeg hA hy1
    rw [eval_comp_lin, hyw] at hD0
    rw [eval_comp_lin, eval_comp_lin, hyw] at hE
    refine ⟨hD0, hE.trans ?_⟩
    have hinv : (Valued.v y)⁻¹ ≤ 𝔭 ^ (m - k) := by
      rw [hvy, inv_div, pow_sub₀ _ h𝔭0 hkm]
      simp only [div_eq_mul_inv]
      exact mul_le_mul_right ((inv_le_inv₀ hwpos (pow_pos h𝔭pos k)).2 hwk) _
    calc gauss (Ni.comp L) / gauss (Qi.comp L) * (Valued.v y)⁻¹ ≤ Valued.v b * 𝔭 ^ (m - k) :=
          mul_le_mul' hgauss hinv
      _ = 𝔭 ^ (m - k) * Valued.v b := mul_comm _ _

  have hsplit : ∀ w : K, w ∈ affinoid ϖ m →
      Qo.eval w ≠ 0 ∧ r.evalAt w = Ni.eval w / Qi.eval w + No.eval w / Qo.eval w := by
    intro w hw
    obtain ⟨-, h2, h3⟩ := eval_splitP p r.num r.den (hr w hw)
    exact ⟨h2, h3⟩

  refine ⟨⟨No, Qo⟩, QoutP_ne_zero p hr0, ?_, ?_, ?_, ?_⟩
  ·
    intro w hw h0
    apply hr w hw
    show r.den.eval w = 0
    rw [← QinP_mul_QoutP p r.den, eval_mul]
    exact mul_eq_zero_of_right _ h0
  ·
    intro w hw
    obtain ⟨hQo, hrw⟩ := hsplit w hw
    have hwt : 𝔭 ^ m ≤ Valued.v (w - t) := p_pow_le_v_sub_of_mem_affinoid ϖ m hw a
    obtain ⟨-, hE⟩ := est w m le_rfl hwt
    rw [Nat.sub_self, pow_zero, one_mul] at hE
    have : RatPair.evalAt ⟨No, Qo⟩ w = r.evalAt w - Ni.eval w / Qi.eval w := by
      rw [hrw]; show No.eval w / Qo.eval w = _; ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le (hb w hw) hE)
  ·
    have hcount := card_filter_roots_QoutP' p hr0 (fun α => Valued.v α ≤ 𝔭⁻¹ ^ m)
    have hpos : 0 < ((QinP p r.den).roots.filter (fun α => Valued.v α ≤ 𝔭⁻¹ ^ m)).card := by
      rw [Multiset.card_pos_iff_exists_mem]
      refine ⟨α₀, Multiset.mem_filter.2 ⟨(mem_roots_QinP p).2 ⟨hα₀, ?_⟩, hα₀D⟩⟩
      show Valued.v (α₀ - t) < 𝔭 ^ m
      exact hαa
    show ((QoutP p r.den).roots.filter _).card < _
    omega
  ·
    intro z z₀ hz hz₀
    obtain ⟨-, hrz⟩ := hsplit z (mem_affinoid_of_le ϖ hnm hz)
    obtain ⟨-, hrz₀⟩ := hsplit z₀ (mem_affinoid_of_le ϖ hnm hz₀)
    obtain ⟨-, hEz⟩ := est z n hnm (p_pow_le_v_sub_of_mem_affinoid ϖ n hz a)
    obtain ⟨-, hEz₀⟩ := est z₀ n hnm (p_pow_le_v_sub_of_mem_affinoid ϖ n hz₀ a)
    have : r.evalAt z - r.evalAt z₀ = (Ni.eval z / Qi.eval z - Ni.eval z₀ / Qi.eval z₀) +
        (RatPair.evalAt ⟨No, Qo⟩ z - RatPair.evalAt ⟨No, Qo⟩ z₀) := by
      rw [hrz, hrz₀]; show _ = _ + (No.eval z / Qo.eval z - No.eval z₀ / Qo.eval z₀); ring
    rw [this]
    refine (Valuation.map_add _ _ _).trans (max_le_max ?_ le_rfl)
    exact (Valuation.map_sub _ _ _).trans (max_le hEz hEz₀)

end Peel

end RatOsc

namespace RatOsc
open IdAnn Polynomial
variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K] (ϖ : PseudoUniformizer K₀ K)

theorem p_pow_mul_inv_pow_eq {n m : ℕ} (hnm : n ≤ m) :
    Valued.v (algebraMap K₀ K ϖ.ϖ) ^ m * (Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n)⁻¹
      = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (m - n) := by
  have h0 : Valued.v (algebraMap K₀ K ϖ.ϖ) ≠ 0 := ϖ.pos.ne'
  rw [← pow_sub₀ _ h0 hnm]

theorem osc_base (m n : ℕ) (hnm : n ≤ m) (T : Finset K₀)
    (hT : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ m) (b : K)
    (r : RatPair K) (hr0 : r.den ≠ 0) (hr : r.IsPoleFreeOn (affinoid ϖ m))
    (hb : ∀ w : K, w ∈ affinoid ϖ m → Valued.v (r.evalAt w) ≤ Valued.v b)
    (hroots : ∀ α ∈ r.den.roots, (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m < Valued.v α)
    {z z₀ : K} (hz : z ∈ affinoid ϖ n) (hz₀ : z₀ ∈ affinoid ϖ n) :
    Valued.v (r.evalAt z - r.evalAt z₀) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (m - n) * Valued.v b := by

  set p : K := algebraMap K₀ K ϖ.ϖ with hp
  have hpos : 0 < Valued.v p := ϖ.pos
  have hvp : Valued.v p ≠ 0 := hpos.ne'
  have hp0 : p ≠ 0 := (Valuation.ne_zero_iff _).mp hvp
  set πi : K := p⁻¹ ^ m with hπi
  have hπi0 : πi ≠ 0 := pow_ne_zero _ (inv_ne_zero hp0)
  have hvπi : Valued.v πi = (Valued.v p)⁻¹ ^ m := by rw [hπi, map_pow, map_inv₀]
  set Ntil : K[X] := r.num.comp (C πi * X) with hN
  set Dtil : K[X] := r.den.comp (C πi * X) with hD
  have hD0 : Dtil ≠ 0 := by
    rw [hD, Ne, comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_of_ne_zero hπi0)]; exact hr0
  have hgauss : gauss Ntil ≤ Valued.v b * gauss Dtil :=
    gauss_le_of_forall_lt_roots ϖ m T hT r hr0 hr b hb hroots
  have hDroots : ∀ β ∈ Dtil.roots, 1 < Valued.v β := lt_roots_comp_outer ϖ m r hr0 hroots

  set y : K := p ^ m * z with hy
  set y₀ : K := p ^ m * z₀ with hy₀
  have hzy : πi * y = z := by
    rw [hπi, hy, ← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hp0), one_mul]
  have hzy₀ : πi * y₀ = z₀ := by
    rw [hπi, hy₀, ← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hp0), one_mul]
  have hvy : ∀ {w : K}, w ∈ affinoid ϖ n → Valued.v (p ^ m * w) ≤ 1 := by
    intro w hw
    rw [map_mul, map_pow]
    have h1 := v_le_of_mem_affinoid ϖ n hw
    have h2 : (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m :=
      pow_le_pow_right₀ ((one_le_inv₀ ϖ.pos).2 ϖ.lt_one.le) hnm
    calc Valued.v p ^ m * Valued.v w ≤ Valued.v p ^ m * (Valued.v p)⁻¹ ^ m := by
          exact mul_le_mul_right (h1.trans h2) _
      _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ hvp, one_pow]
  obtain ⟨hDy, hDy₀, hest⟩ :=
    IdAnn.v_div_sub_div_le_of_one_lt_roots Ntil Dtil hD0 hDroots (hvy hz) (hvy hz₀)

  have hevN : ∀ w : K, Ntil.eval (p ^ m * w) = r.num.eval w := by
    intro w; rw [hN, eval_comp_C_mul_X, hπi, ← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hp0), one_mul]
  have hevD : ∀ w : K, Dtil.eval (p ^ m * w) = r.den.eval w := by
    intro w; rw [hD, eval_comp_C_mul_X, hπi, ← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hp0), one_mul]
  have hval : r.evalAt z - r.evalAt z₀ = Ntil.eval y / Dtil.eval y - Ntil.eval y₀ / Dtil.eval y₀ := by
    simp only [RatPair.evalAt, hy, hy₀, hevN, hevD]
  rw [hval]
  refine hest.trans ?_

  have hgD : gauss Dtil ≠ 0 := gauss_ne_zero hD0
  have hratio : gauss Ntil / gauss Dtil ≤ Valued.v b := by
    rw [div_le_iff₀ (zero_lt_iff.mpr hgD)]; exact hgauss
  have hdiff : Valued.v (y - y₀) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (m - n) := by
    rw [hy, hy₀, ← mul_sub, map_mul, map_pow]
    have h1 : Valued.v (z - z₀) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n :=
      (Valuation.map_sub _ _ _).trans (max_le (v_le_of_mem_affinoid ϖ n hz) (v_le_of_mem_affinoid ϖ n hz₀))
    calc Valued.v p ^ m * Valued.v (z - z₀) ≤ Valued.v p ^ m * (Valued.v p)⁻¹ ^ n :=
          mul_le_mul_right h1 _
      _ = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (m - n) := by
          rw [inv_pow]; exact p_pow_mul_inv_pow_eq ϖ hnm
  calc gauss Ntil / gauss Dtil * Valued.v (y - y₀) ≤ Valued.v b * Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (m - n) :=
        mul_le_mul' hratio hdiff
    _ = Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (m - n) * Valued.v b := mul_comm _ _

theorem osc_induction (m n : ℕ) (hnm : n ≤ m) (T : Finset K₀)
    (hT : ∀ a : K₀, Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m →
      ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ m) (b : K) :
    ∀ (N : ℕ) (r : RatPair K), r.den ≠ 0 → r.IsPoleFreeOn (affinoid ϖ m) →
      (∀ w : K, w ∈ affinoid ϖ m → Valued.v (r.evalAt w) ≤ Valued.v b) →
      (r.den.roots.filter (fun α => Valued.v α ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m)).card ≤ N →
      ∀ z z₀ : K, z ∈ affinoid ϖ n → z₀ ∈ affinoid ϖ n →
        Valued.v (r.evalAt z - r.evalAt z₀) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (m - n) * Valued.v b := by
  intro N
  induction N with
  | zero =>
    intro r hr0 hr hb hcard z z₀ hz hz₀
    have hroots : ∀ α ∈ r.den.roots, (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m < Valued.v α := by
      intro α hα
      by_contra hle
      rw [not_lt] at hle
      have hmem : α ∈ r.den.roots.filter (fun α => Valued.v α ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m) :=
        Multiset.mem_filter.mpr ⟨hα, hle⟩
      have := Multiset.card_pos_iff_exists_mem.mpr ⟨α, hmem⟩
      omega
    exact osc_base ϖ m n hnm T hT b r hr0 hr hb hroots hz hz₀
  | succ N ih =>
    intro r hr0 hr hb hcard z z₀ hz hz₀
    by_cases hex : ∃ α ∈ r.den.roots, Valued.v α ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m
    · obtain ⟨α₀, hα₀, hα₀D⟩ := hex
      obtain ⟨r', hr0', hr', hb', hcard', hest⟩ := peel_step ϖ m n hnm T hT b r hr0 hr hb α₀ hα₀ hα₀D
      have hcardN : (r'.den.roots.filter
          (fun α => Valued.v α ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m)).card ≤ N := by omega
      have h' := ih r' hr0' hr' hb' hcardN z z₀ hz hz₀
      exact (hest z z₀ hz hz₀).trans (max_le le_rfl h')
    · push Not at hex
      exact osc_base ϖ m n hnm T hT b r hr0 hr hb (fun α hα => hex α hα) hz hz₀

end RatOsc

open CerednikDrinfeld.Omega in

theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K) (n m : ℕ) (hnm : n ≤ m)
    (hfin : ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ m →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ m)
    (r : RatPair K) (hr : r.IsPoleFreeOn (affinoid ϖ m))
    (b : K) (hb : ∀ w : K, w ∈ affinoid ϖ m → Valued.v (r.evalAt w) ≤ Valued.v b)
    {z z₀ : K} (hz : z ∈ affinoid ϖ n) (hz₀ : z₀ ∈ affinoid ϖ n) :
    Valued.v (r.evalAt z - r.evalAt z₀) ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (m - n) * Valued.v b := by
  classical
  obtain ⟨T, hT⟩ := hfin
  have hne : (affinoid ϖ m).Nonempty := ⟨z, RatOsc.mem_affinoid_of_le ϖ hnm hz⟩
  have hr0 : r.den ≠ 0 := by
    intro h0
    obtain ⟨w, hw⟩ := hne
    exact hr w hw (by rw [h0, Polynomial.eval_zero])
  exact RatOsc.osc_induction ϖ m n hnm T hT b _ r hr0 hr hb le_rfl z z₀ hz hz₀

end
end S_CerednikDrinfeld_Omega_RatPair_v_evalAt_sub_evalAt_le_mul_of_isPoleFreeOn_affinoid
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_RatPair_v_evalAt_sub_evalAt_le_mul_of_isPoleFreeOn_affinoid (solution)
