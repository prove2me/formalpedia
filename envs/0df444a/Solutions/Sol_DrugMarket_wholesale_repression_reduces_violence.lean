-- Prove2me | solution 1 for DrugMarket.wholesale_repression_reduces_violence
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:33:34.771428+00:00
-- url     : https://prove2.me/submissions/c80eeb06-0a0d-4619-8216-900dc4e27d7e

import Mathlib
import Definitions.Def_drug_market_model
import Definitions.Def_drug_market_equilibrium
namespace DrugMarket
theorem wholesale_repression_reduces_violence (q s t c v_r v_ra v_rb : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hs : 0 < s) (ht : 0 < t) (hvr : 0 < v_r) (hvra : 0 < v_ra) (hvrb : 0 < v_rb) (hmarg : 0 < eqMarginA q s t c v_ra v_rb) :
  deriv (fun vra => eqViolenceA q s t c v_r vra v_rb) v_ra = qHat q s v_r (eqGrossProfitA q s t c v_ra v_rb) * deriv (fun vra => eqGrossProfitA q s t c vra v_rb) v_ra ∧ deriv (fun vra => eqViolenceA q s t c v_r vra v_rb) v_ra < 0 := by
  have hq0 : 0 < q := hq.1
  have hlog : Real.log q < 0 := Real.log_neg hq.1 hq.2
  have key : ∀ v : ℝ, 0 < v → ∃ k' : ℝ, 0 < k' ∧ HasDerivAt (fun x => kappa q s x) k' v := by
    intro v hv
    have hρ : HasDerivAt (fun x : ℝ => q ^ (1 / x)) (q ^ (1 / v) * Real.log q * (-(v ^ 2)⁻¹)) v := by
      have h1 : HasDerivAt (fun x : ℝ => 1 / x) (-(v ^ 2)⁻¹) v := by
        simpa [one_div] using hasDerivAt_inv hv.ne'
      exact (Real.hasStrictDerivAt_const_rpow hq0 (1 / v)).hasDerivAt.comp v h1
    set ρ := q ^ (1 / v) with hρdef
    set ρ' := q ^ (1 / v) * Real.log q * (-(v ^ 2)⁻¹) with hρ'def
    have hρpos : 0 < ρ := Real.rpow_pos_of_pos hq0 _
    have hρlt : ρ < 1 := Real.rpow_lt_one hq0.le hq.2 (by positivity)
    have hρ'pos : 0 < ρ' := by
      rw [hρ'def]
      have : 0 < (v ^ 2)⁻¹ := by positivity
      have h2 : 0 < q ^ (1 / v) * (-Real.log q) := mul_pos hρpos (by linarith)
      nlinarith
    have hden : (fun x : ℝ => 1 - q ^ (1 / x)) v ≠ 0 := by simp only; rw [← hρdef]; linarith
    have hk := (hρ.const_mul s).div ((hasDerivAt_const v (1 : ℝ)).sub hρ) hden
    have e : (fun x => kappa q s x) = fun x => s * q ^ (1 / x) / (1 - q ^ (1 / x)) := rfl
    refine ⟨(s * ρ' * (1 - ρ) - s * ρ * (0 - ρ')) / (1 - ρ) ^ 2, ?_, ?_⟩
    · apply div_pos
      · nlinarith [mul_pos hs hρ'pos, mul_pos (mul_pos hs hρpos) hρ'pos]
      · have : 0 < 1 - ρ := by linarith
        positivity
    · rw [e]; exact hk
  have hL : Real.log q < 0 := Real.log_neg hq.1 hq.2
  have hLne : Real.log q ≠ 0 := hL.ne
  have hV : ∀ g : ℝ, 0 ≤ g → HasDerivAt (fun g => violenceBR q s v_r g) (qHat q s v_r g) g := by
    intro g hg
    have hgs : 0 < g + s := by linarith
    have h1 : HasDerivAt (fun x => Real.log q * (x + s)) (Real.log q * 1) g :=
      ((hasDerivAt_id g).add_const s).const_mul _
    have h2 := (hasDerivAt_const g (-v_r)).div h1 (mul_ne_zero hLne hgs.ne')
    have hqpos : 0 < qHat q s v_r g := by
      unfold qHat
      exact div_pos_of_neg_of_neg (by linarith) (mul_neg_of_neg_of_pos hL hgs)
    have h3 := h2.log hqpos.ne'
    have h4 := (h3.const_mul v_r).div_const (Real.log q)
    refine h4.congr_deriv ?_
    simp only [Pi.div_apply]
    unfold qHat
    field_simp
    ring
  obtain ⟨ka, hka, hda⟩ := key v_ra hvra
  have hM : HasDerivAt (fun vra => eqMarginA q s t c vra v_rb) ((0 - ka) / 9) v_ra := by
    unfold eqMarginA
    exact (((hasDerivAt_const v_ra _).sub hda).div_const 9).const_add _
  have hG : HasDerivAt (fun vra => eqGrossProfitA q s t c vra v_rb)
      ((2 : ℕ) * eqMarginA q s t c v_ra v_rb ^ (2 - 1) * ((0 - ka) / 9) / (2 * t)) v_ra := by
    unfold eqGrossProfitA
    exact (hM.pow 2).div_const (2 * t)
  have hGneg : (2 : ℕ) * eqMarginA q s t c v_ra v_rb ^ (2 - 1) * ((0 - ka) / 9) / (2 * t) < 0 := by
    apply div_neg_of_neg_of_pos _ (by positivity)
    norm_num
    nlinarith
  have hg0 : 0 ≤ eqGrossProfitA q s t c v_ra v_rb := by unfold eqGrossProfitA; positivity
  have hqp : 0 < qHat q s v_r (eqGrossProfitA q s t c v_ra v_rb) := by
    unfold qHat
    exact div_pos_of_neg_of_neg (by linarith) (mul_neg_of_neg_of_pos hL (by linarith))
  have hc : HasDerivAt (fun vra => eqViolenceA q s t c v_r vra v_rb)
      (qHat q s v_r (eqGrossProfitA q s t c v_ra v_rb) *
        ((2 : ℕ) * eqMarginA q s t c v_ra v_rb ^ (2 - 1) * ((0 - ka) / 9) / (2 * t))) v_ra := by
    have h := (hV (eqGrossProfitA q s t c v_ra v_rb) hg0).comp v_ra hG
    exact h
  rw [hc.deriv, hG.deriv]
  exact ⟨rfl, mul_neg_of_pos_of_neg hqp hGneg⟩

end DrugMarket

open DrugMarket in
theorem solution (q s t c v_r v_ra v_rb : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hs : 0 < s) (ht : 0 < t) (hvr : 0 < v_r) (hvra : 0 < v_ra) (hvrb : 0 < v_rb) (hmarg : 0 < eqMarginA q s t c v_ra v_rb) :
  deriv (fun vra => eqViolenceA q s t c v_r vra v_rb) v_ra = qHat q s v_r (eqGrossProfitA q s t c v_ra v_rb) * deriv (fun vra => eqGrossProfitA q s t c vra v_rb) v_ra ∧ deriv (fun vra => eqViolenceA q s t c v_r vra v_rb) v_ra < 0 := by
  have hq0 : 0 < q := hq.1
  have hlog : Real.log q < 0 := Real.log_neg hq.1 hq.2
  have key : ∀ v : ℝ, 0 < v → ∃ k' : ℝ, 0 < k' ∧ HasDerivAt (fun x => kappa q s x) k' v := by
    intro v hv
    have hρ : HasDerivAt (fun x : ℝ => q ^ (1 / x)) (q ^ (1 / v) * Real.log q * (-(v ^ 2)⁻¹)) v := by
      have h1 : HasDerivAt (fun x : ℝ => 1 / x) (-(v ^ 2)⁻¹) v := by
        simpa [one_div] using hasDerivAt_inv hv.ne'
      exact (Real.hasStrictDerivAt_const_rpow hq0 (1 / v)).hasDerivAt.comp v h1
    set ρ := q ^ (1 / v) with hρdef
    set ρ' := q ^ (1 / v) * Real.log q * (-(v ^ 2)⁻¹) with hρ'def
    have hρpos : 0 < ρ := Real.rpow_pos_of_pos hq0 _
    have hρlt : ρ < 1 := Real.rpow_lt_one hq0.le hq.2 (by positivity)
    have hρ'pos : 0 < ρ' := by
      rw [hρ'def]
      have : 0 < (v ^ 2)⁻¹ := by positivity
      have h2 : 0 < q ^ (1 / v) * (-Real.log q) := mul_pos hρpos (by linarith)
      nlinarith
    have hden : (fun x : ℝ => 1 - q ^ (1 / x)) v ≠ 0 := by simp only; rw [← hρdef]; linarith
    have hk := (hρ.const_mul s).div ((hasDerivAt_const v (1 : ℝ)).sub hρ) hden
    have e : (fun x => kappa q s x) = fun x => s * q ^ (1 / x) / (1 - q ^ (1 / x)) := rfl
    refine ⟨(s * ρ' * (1 - ρ) - s * ρ * (0 - ρ')) / (1 - ρ) ^ 2, ?_, ?_⟩
    · apply div_pos
      · nlinarith [mul_pos hs hρ'pos, mul_pos (mul_pos hs hρpos) hρ'pos]
      · have : 0 < 1 - ρ := by linarith
        positivity
    · rw [e]; exact hk
  have hL : Real.log q < 0 := Real.log_neg hq.1 hq.2
  have hLne : Real.log q ≠ 0 := hL.ne
  have hV : ∀ g : ℝ, 0 ≤ g → HasDerivAt (fun g => violenceBR q s v_r g) (qHat q s v_r g) g := by
    intro g hg
    have hgs : 0 < g + s := by linarith
    have h1 : HasDerivAt (fun x => Real.log q * (x + s)) (Real.log q * 1) g :=
      ((hasDerivAt_id g).add_const s).const_mul _
    have h2 := (hasDerivAt_const g (-v_r)).div h1 (mul_ne_zero hLne hgs.ne')
    have hqpos : 0 < qHat q s v_r g := by
      unfold qHat
      exact div_pos_of_neg_of_neg (by linarith) (mul_neg_of_neg_of_pos hL hgs)
    have h3 := h2.log hqpos.ne'
    have h4 := (h3.const_mul v_r).div_const (Real.log q)
    refine h4.congr_deriv ?_
    simp only [Pi.div_apply]
    unfold qHat
    field_simp
    ring
  obtain ⟨ka, hka, hda⟩ := key v_ra hvra
  have hM : HasDerivAt (fun vra => eqMarginA q s t c vra v_rb) ((0 - ka) / 9) v_ra := by
    unfold eqMarginA
    exact (((hasDerivAt_const v_ra _).sub hda).div_const 9).const_add _
  have hG : HasDerivAt (fun vra => eqGrossProfitA q s t c vra v_rb)
      ((2 : ℕ) * eqMarginA q s t c v_ra v_rb ^ (2 - 1) * ((0 - ka) / 9) / (2 * t)) v_ra := by
    unfold eqGrossProfitA
    exact (hM.pow 2).div_const (2 * t)
  have hGneg : (2 : ℕ) * eqMarginA q s t c v_ra v_rb ^ (2 - 1) * ((0 - ka) / 9) / (2 * t) < 0 := by
    apply div_neg_of_neg_of_pos _ (by positivity)
    norm_num
    nlinarith
  have hg0 : 0 ≤ eqGrossProfitA q s t c v_ra v_rb := by unfold eqGrossProfitA; positivity
  have hqp : 0 < qHat q s v_r (eqGrossProfitA q s t c v_ra v_rb) := by
    unfold qHat
    exact div_pos_of_neg_of_neg (by linarith) (mul_neg_of_neg_of_pos hL (by linarith))
  have hc : HasDerivAt (fun vra => eqViolenceA q s t c v_r vra v_rb)
      (qHat q s v_r (eqGrossProfitA q s t c v_ra v_rb) *
        ((2 : ℕ) * eqMarginA q s t c v_ra v_rb ^ (2 - 1) * ((0 - ka) / 9) / (2 * t))) v_ra := by
    have h := (hV (eqGrossProfitA q s t c v_ra v_rb) hg0).comp v_ra hG
    exact h
  rw [hc.deriv, hG.deriv]
  exact ⟨rfl, mul_neg_of_pos_of_neg hqp hGneg⟩
