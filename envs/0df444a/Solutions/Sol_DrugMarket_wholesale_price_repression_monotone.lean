-- Prove2me | solution 1 for DrugMarket.wholesale_price_repression_monotone
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:30:11.491375+00:00
-- url     : https://prove2.me/submissions/d4044b48-e440-4a03-aca5-93cd8fcdfb8c

import Mathlib
import Definitions.Def_drug_market_model
import Definitions.Def_drug_market_equilibrium
namespace DrugMarket
theorem wholesale_price_repression_monotone (q s t c v_ra v_rb : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hs : 0 < s) (ht : 0 < t) (hvra : 0 < v_ra) (hvrb : 0 < v_rb) :
  deriv (fun vra => wholesalePriceA q s t c vra v_rb) v_ra > 0 ∧ deriv (fun vrb => wholesalePriceB q s t c v_ra vrb) v_rb > 0 := by
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
  obtain ⟨ka, hka, hda⟩ := key v_ra hvra
  obtain ⟨kb, hkb, hdb⟩ := key v_rb hvrb
  constructor
  · have : HasDerivAt (fun vra => wholesalePriceA q s t c vra v_rb) ((2 * ka + 0) / 3) v_ra := by
      unfold wholesalePriceA
      exact (((hda.const_mul 2).add (hasDerivAt_const v_ra _)).div_const 3).const_add _
    rw [this.deriv]; linarith
  · have : HasDerivAt (fun vrb => wholesalePriceB q s t c v_ra vrb) ((2 * kb + 0) / 3) v_rb := by
      unfold wholesalePriceB
      exact (((hdb.const_mul 2).add (hasDerivAt_const v_rb _)).div_const 3).const_add _
    rw [this.deriv]; linarith

end DrugMarket

open DrugMarket in
theorem solution (q s t c v_ra v_rb : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hs : 0 < s) (ht : 0 < t) (hvra : 0 < v_ra) (hvrb : 0 < v_rb) :
  deriv (fun vra => wholesalePriceA q s t c vra v_rb) v_ra > 0 ∧ deriv (fun vrb => wholesalePriceB q s t c v_ra vrb) v_rb > 0 := by
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
  obtain ⟨ka, hka, hda⟩ := key v_ra hvra
  obtain ⟨kb, hkb, hdb⟩ := key v_rb hvrb
  constructor
  · have : HasDerivAt (fun vra => wholesalePriceA q s t c vra v_rb) ((2 * ka + 0) / 3) v_ra := by
      unfold wholesalePriceA
      exact (((hda.const_mul 2).add (hasDerivAt_const v_ra _)).div_const 3).const_add _
    rw [this.deriv]; linarith
  · have : HasDerivAt (fun vrb => wholesalePriceB q s t c v_ra vrb) ((2 * kb + 0) / 3) v_rb := by
      unfold wholesalePriceB
      exact (((hdb.const_mul 2).add (hasDerivAt_const v_rb _)).div_const 3).const_add _
    rw [this.deriv]; linarith
