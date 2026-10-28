-- Prove2me | solution 1 for DQI.Semicircle.eq_39_40
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T03:29:23.336401+00:00
-- url     : https://prove2.me/submissions/04320dec-7795-4eba-a67c-53e812674066

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting

namespace Aux_DQIs3940
open DQI.Semicircle

lemma sum_ite_F (p : ℕ) [Fact p.Prime] (F : Finset (ZMod p)) (X Y : ℝ) :
    ∑ a : ZMod p, (if a ∈ F then X else Y) = F.card * X + (p - F.card) * Y := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have h1 : (Finset.univ.filter (fun a : ZMod p => a ∈ F)).card = F.card := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod p)))
    (fun a : ZMod p => a ∈ F)
  rw [Finset.card_univ, ZMod.card, h1] at h2
  have h3 : ((Finset.univ.filter (fun a : ZMod p => ¬ a ∈ F)).card : ℝ) = p - F.card := by
    have : ((F.card + (Finset.univ.filter (fun a : ZMod p => ¬ a ∈ F)).card : ℕ) : ℝ) = p := by
      exact_mod_cast h2
    push_cast at this
    linarith
  rw [h1, h3]

end Aux_DQIs3940

open DQI.Semicircle Aux_DQIs3940 in
theorem solution (p : ℕ) [Fact p.Prime] (m : ℕ) (F : Fin m → Finset (ZMod p)) (r : ℕ)
    (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p) (i : Fin m) :
    fbar F i = 2 * (r : ℝ) / p - 1 ∧
    phi F i = Real.sqrt (4 * r * (1 - (r : ℝ) / p)) ∧
    ∑ x : ZMod p, g F i x ^ 2 = 1 ∧
    gt F i 0 = 0 ∧
    ∑ y : ZMod p, ‖gt F i y‖ ^ 2 = 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpne : (p : ℝ) ≠ 0 := hp0.ne'
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrp' : (r : ℝ) < p := by exact_mod_cast hrp
  have hsumf : ∑ a : ZMod p, fval F i a = 2 * r - p := by
    unfold fval
    rw [sum_ite_F, hF]; ring
  have hfbar : fbar F i = 2 * (r : ℝ) / p - 1 := by
    unfold fbar; rw [hsumf]; field_simp
  have hsq : ∀ a, (fval F i a - fbar F i) ^ 2 =
      if a ∈ F i then (1 - fbar F i) ^ 2 else (-1 - fbar F i) ^ 2 := by
    intro a; unfold fval; split_ifs <;> rfl
  have hS : ∑ a : ZMod p, (fval F i a - fbar F i) ^ 2 = 4 * r * (1 - (r : ℝ) / p) := by
    rw [Finset.sum_congr rfl (fun a _ => hsq a), sum_ite_F, hF, hfbar]
    field_simp
    ring
  have hSpos : 0 < 4 * (r : ℝ) * (1 - (r : ℝ) / p) := by
    have : (r : ℝ) / p < 1 := by rw [div_lt_one hp0]; exact hrp'
    have : 0 < 1 - (r : ℝ) / p := by linarith
    positivity
  have hphi : phi F i = Real.sqrt (4 * r * (1 - (r : ℝ) / p)) := by
    unfold phi; rw [hS]
  have hphipos : 0 < phi F i := by rw [hphi]; exact Real.sqrt_pos.2 hSpos
  have hphi2 : phi F i ^ 2 = ∑ a : ZMod p, (fval F i a - fbar F i) ^ 2 := by
    rw [hphi, Real.sq_sqrt hSpos.le, hS]
  have hg2 : ∑ x : ZMod p, g F i x ^ 2 = 1 := by
    unfold g
    simp only [div_pow]
    rw [← Finset.sum_div, ← hphi2, div_self (pow_ne_zero 2 hphipos.ne')]
  have hgsum : ∑ x : ZMod p, g F i x = 0 := by
    unfold g
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul]
    unfold fbar
    field_simp
    ring
  refine ⟨hfbar, hphi, hg2, ?_, ?_⟩
  · unfold gt
    have h0 : ∀ x : ZMod p, omega (0 * x) = 1 := by
      intro x; simp [omega]
    simp only [h0, one_mul]
    rw [← Complex.ofReal_sum, hgsum]; simp
  · -- Parseval
    set ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar with hψ
    have hω : ∀ a : ZMod p, omega a = ψ a := by
      intro a
      rw [hψ, ZMod.stdAddChar_apply, ZMod.toCircle_apply]
      rfl
    have hprim : ψ.IsPrimitive := ZMod.isPrimitive_stdAddChar p
    set c : ℂ := 1 / (Real.sqrt p : ℂ) with hc
    have hcc : c * (starRingEnd ℂ) c = 1 / p := by
      rw [hc, map_div₀, map_one, Complex.conj_ofReal]
      have : ((Real.sqrt p : ℝ) : ℂ) * ((Real.sqrt p : ℝ) : ℂ) = (p : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp0.le]; simp
      rw [div_mul_div_comm, one_mul, this]
    have hprod : ∀ y : ZMod p, gt F i y * (starRingEnd ℂ) (gt F i y) =
        c * (starRingEnd ℂ) c * ∑ x : ZMod p, ∑ x' : ZMod p,
          ψ ((x - x') * y) * ((g F i x * g F i x' : ℝ) : ℂ) := by
      intro y
      unfold gt
      rw [← hc, map_mul, map_sum]
      rw [show c * (∑ x, omega (y * x) * ((g F i x : ℝ) : ℂ)) *
          ((starRingEnd ℂ) c * ∑ x, (starRingEnd ℂ) (omega (y * x) * ((g F i x : ℝ) : ℂ))) =
          c * (starRingEnd ℂ) c * ((∑ x, omega (y * x) * ((g F i x : ℝ) : ℂ)) *
          ∑ x, (starRingEnd ℂ) (omega (y * x) * ((g F i x : ℝ) : ℂ))) by ring]
      congr 1
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro x' _
      rw [map_mul, Complex.conj_ofReal, hω, hω, ← AddChar.map_neg_eq_conj,
        show (x - x') * y = y * x + -(y * x') by ring, AddChar.map_add_eq_mul]
      push_cast
      ring
    have hsumy : ∑ y : ZMod p, gt F i y * (starRingEnd ℂ) (gt F i y) = 1 := by
      rw [Finset.sum_congr rfl (fun y _ => hprod y), ← Finset.mul_sum]
      have : ∑ y : ZMod p, ∑ x : ZMod p, ∑ x' : ZMod p,
          ψ ((x - x') * y) * ((g F i x * g F i x' : ℝ) : ℂ) =
          ∑ x : ZMod p, ∑ x' : ZMod p, ((g F i x * g F i x' : ℝ) : ℂ) *
            ∑ y : ZMod p, ψ (y * (x - x')) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro x _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro x' _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro y _
        rw [mul_comm (x - x') y]; ring
      rw [this]
      simp only [AddChar.sum_mulShift _ hprim, sub_eq_zero, Nat.cast_ite, Nat.cast_zero, mul_ite,
        mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, ZMod.card]
      rw [hcc]
      have : ∑ x : ZMod p, ((g F i x * g F i x : ℝ) : ℂ) * (p : ℂ) =
          (p : ℂ) * ((∑ x : ZMod p, g F i x ^ 2 : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro x _
        push_cast; ring
      rw [this, hg2, Complex.ofReal_one, mul_one]
      have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hpne
      field_simp
    have : ((∑ y : ZMod p, ‖gt F i y‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← hsumy, Complex.ofReal_sum]
      apply Finset.sum_congr rfl; intro y _
      rw [Complex.mul_conj', Complex.ofReal_pow]
    exact_mod_cast this
