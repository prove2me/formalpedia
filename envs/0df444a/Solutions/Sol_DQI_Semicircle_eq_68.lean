-- Prove2me | solution 1 for DQI.Semicircle.eq_68
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T22:01:20.159724+00:00
-- url     : https://prove2.me/submissions/2df273c5-8df5-4f01-804b-74596538ee41

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting

namespace Aux_DQI_Semicircle_eq_68

open DQI.Semicircle Polynomial

variable {p : ℕ} [Fact p.Prime] {m : ℕ}

lemma omega_eq (a : ZMod p) : omega a = (ZMod.stdAddChar (N := p) : AddChar (ZMod p) ℂ) a := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  rfl

lemma parseval (h : ZMod p → ℝ) :
    ∑ y : ZMod p, ‖∑ x : ZMod p, omega (y * x) * (h x : ℂ)‖ ^ 2 = (p : ℝ) * ∑ x, (h x) ^ 2 := by
  have hp0 : 0 < ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n]; exact (Fact.out : p.Prime).pos
  have hconj : ∀ a : ZMod p, (starRingEnd ℂ) ((ZMod.stdAddChar (N := p) : AddChar (ZMod p) ℂ) a) =
      (ZMod.stdAddChar (N := p) : AddChar (ZMod p) ℂ) (-a) := by
    intro a
    rw [AddChar.starComp_apply hp0, AddChar.inv_apply]
  have key : ∀ y : ZMod p, ((‖∑ x : ZMod p, omega (y * x) * (h x : ℂ)‖ : ℝ) : ℂ) ^ 2 =
      ∑ x : ZMod p, ∑ x' : ZMod p,
        (ZMod.stdAddChar (N := p) : AddChar (ZMod p) ℂ) (y * (x - x')) * ((h x * h x' : ℝ) : ℂ) := by
    intro y
    rw [← Complex.mul_conj']
    simp only [omega_eq, map_sum, map_mul, hconj, Complex.conj_ofReal]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro x' _
    rw [show y * (x - x') = y * x + -(y * x') by ring, AddChar.map_add_eq_mul]
    push_cast
    ring
  apply Complex.ofReal_injective
  push_cast
  rw [Finset.sum_congr rfl (fun y _ => key y), Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  rw [Finset.sum_eq_single x]
  · rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar p), sub_self, if_pos rfl, ZMod.card]
    push_cast
    ring
  · intro x' _ hx'
    rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar p),
      if_neg (sub_ne_zero.mpr (Ne.symm hx'))]
    simp
  · intro hx
    exact absurd (Finset.mem_univ x) hx

lemma g_props (F : Fin m → Finset (ZMod p)) (r : ℕ) (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r)
    (hrp : r < p) (i : Fin m) :
    ∑ a, g F i a = 0 ∧ ∑ a, (g F i a) ^ 2 = 1 := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hs0 : ∑ a, (fval F i a - fbar F i) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    unfold fbar
    rw [← mul_assoc, mul_one_div_cancel hp, one_mul, sub_self]
  obtain ⟨a, ha⟩ : (F i).Nonempty := Finset.card_pos.mp (by rw [hF]; omega)
  obtain ⟨b, hb⟩ : ∃ b, b ∉ F i := by
    by_contra hcon
    push_neg at hcon
    have h1 : F i = Finset.univ := Finset.eq_univ_of_forall hcon
    have h2 := congrArg Finset.card h1
    rw [hF, Finset.card_univ, hcard] at h2
    omega
  have hab : a ≠ b := fun h => hb (h ▸ ha)
  have hle : (fval F i a - fbar F i) ^ 2 + (fval F i b - fbar F i) ^ 2 ≤
      ∑ x, (fval F i x - fbar F i) ^ 2 := by
    have := Finset.sum_le_sum_of_subset_of_nonneg (s := {a, b}) (t := Finset.univ)
      (f := fun x => (fval F i x - fbar F i) ^ 2) (Finset.subset_univ _)
      (fun _ _ _ => sq_nonneg _)
    rw [Finset.sum_pair hab] at this
    exact this
  have hfa : fval F i a = 1 := if_pos ha
  have hfb : fval F i b = -1 := if_neg hb
  rw [hfa, hfb] at hle
  have hV : 0 < ∑ x, (fval F i x - fbar F i) ^ 2 := by nlinarith [sq_nonneg (fbar F i)]
  constructor
  · unfold g
    rw [← Finset.sum_div, hs0, zero_div]
  · unfold g
    simp only [div_pow]
    rw [← Finset.sum_div]
    unfold phi
    rw [Real.sq_sqrt hV.le, div_self hV.ne']

lemma gt_zero (F : Fin m → Finset (ZMod p)) (i : Fin m) (hg : ∑ a, g F i a = 0) :
    gt F i 0 = 0 := by
  unfold gt
  have h0 : ∀ x : ZMod p, omega (0 * x) = 1 := by
    intro x
    simp [omega]
  simp only [h0, one_mul]
  rw [← Complex.ofReal_sum, hg]
  simp

lemma gt_parseval (F : Fin m → Finset (ZMod p)) (i : Fin m) (hg2 : ∑ a, (g F i a) ^ 2 = 1) :
    ∑ y, ‖gt F i y‖ ^ 2 = 1 := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h1 : ∀ y, ‖gt F i y‖ ^ 2 =
      (1 / (p : ℝ)) * ‖∑ x : ZMod p, omega (y * x) * (g F i x : ℂ)‖ ^ 2 := by
    intro y
    unfold gt
    rw [norm_mul, mul_pow]
    congr 1
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [Finset.sum_congr rfl (fun y _ => h1 y), ← Finset.mul_sum, parseval, hg2, mul_one, one_div,
    inv_mul_cancel₀ hp]

end Aux_DQI_Semicircle_eq_68

open Aux_DQI_Semicircle_eq_68 Polynomial in
open DQI.Semicircle in
theorem solution (p : ℕ) [Fact p.Prime] (m : ℕ) (F : Fin m → Finset (ZMod p)) (r : ℕ)
    (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p) (k : ℕ) :
    ∑ y ∈ Finset.univ.filter (fun y : Fin m → ZMod p => wt y = k), ‖gtil F y‖ ^ 2 =
      (m.choose k : ℝ) := by
  have hg : ∀ i, ∑ a, g F i a = 0 ∧ ∑ a, (g F i a) ^ 2 = 1 := g_props F r hF hr hrp
  have hsum1 : ∀ i, ∑ a, ‖gt F i a‖ ^ 2 = 1 := fun i => gt_parseval F i (hg i).2
  have h0 : ∀ i, gt F i 0 = 0 := fun i => gt_zero F i (hg i).1
  have hnorm : ∀ y : Fin m → ZMod p, ‖gtil F y‖ ^ 2 =
      ∏ i ∈ Finset.univ.filter (fun i => y i ≠ 0), ‖gt F i (y i)‖ ^ 2 := by
    intro y
    unfold gtil
    rw [norm_prod, ← Finset.prod_pow]
  obtain ⟨Fp, hFp⟩ : ∃ Fp : Fin m → ZMod p → ℝ[X],
      Fp = fun i a => if a ≠ 0 then C (‖gt F i a‖ ^ 2) else X := ⟨_, rfl⟩
  have h1 : ∀ y : Fin m → ZMod p,
      C (∏ i ∈ Finset.univ.filter (fun i => y i ≠ 0), ‖gt F i (y i)‖ ^ 2) *
        X ^ (Finset.univ.filter (fun i => ¬ (y i ≠ 0))).card = ∏ i, Fp i (y i) := by
    intro y
    simp only [hFp]
    rw [Finset.prod_ite, map_prod, Finset.prod_const]
  have h2 : ∀ i, ∑ a, Fp i a = X + 1 := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]
    have e1 : Fp i 0 = X := by simp [hFp]
    have e2 : ∀ a ∈ Finset.univ.erase (0 : ZMod p), Fp i a = C (‖gt F i a‖ ^ 2) := by
      intro a ha
      simp [hFp, Finset.ne_of_mem_erase ha]
    rw [e1, Finset.sum_congr rfl e2, ← map_sum, Finset.sum_erase_eq_sub (Finset.mem_univ _),
      hsum1 i, h0 i, norm_zero]
    simp
  have hpoly : ∑ y : Fin m → ZMod p,
      C (∏ i ∈ Finset.univ.filter (fun i => y i ≠ 0), ‖gt F i (y i)‖ ^ 2) *
        X ^ (Finset.univ.filter (fun i => ¬ (y i ≠ 0))).card = (X + 1 : ℝ[X]) ^ m := by
    rw [Finset.sum_congr rfl (fun y _ => h1 y), ← Fintype.prod_sum Fp,
      Finset.prod_congr rfl (fun i _ => h2 i), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hcoef := congrArg (fun P : ℝ[X] => P.coeff (m - k)) hpoly
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_X_add_one_pow] at hcoef
  have hz : ∀ y : Fin m → ZMod p,
      wt y + (Finset.univ.filter (fun i => ¬ (y i ≠ 0))).card = m := by
    intro y
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
      (fun i => y i ≠ 0)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this
  rw [Finset.sum_filter]
  by_cases hkm : k ≤ m
  · rw [Nat.choose_symm hkm] at hcoef
    rw [← hcoef]
    apply Finset.sum_congr rfl
    intro y _
    have := hz y
    by_cases hw : wt y = k
    · have hc : m - k = (Finset.univ.filter (fun i => ¬ (y i ≠ 0))).card := by omega
      rw [if_pos hw, if_pos hc, hnorm]
    · have hc : ¬ (m - k = (Finset.univ.filter (fun i => ¬ (y i ≠ 0))).card) := by omega
      rw [if_neg hw, if_neg hc]
  · push_neg at hkm
    rw [Nat.choose_eq_zero_of_lt hkm, Nat.cast_zero]
    apply Finset.sum_eq_zero
    intro y _
    have := hz y
    have hw : ¬ (wt y = k) := by omega
    rw [if_neg hw]
