-- Prove2me | solution 1 for DrugMarket.wholesale_price_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:32:08.627299+00:00
-- url     : https://prove2.me/submissions/aa9459dc-d329-4640-8b86-fbced69a88b7

import Mathlib
import Definitions.Def_drug_market_model
import Definitions.Def_drug_market_equilibrium
namespace DrugMarket
theorem wholesale_price_equilibrium (q s t c v_ra v_rb w_a w_b : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hs : 0 < s) (ht : 0 < t) (hvra : 0 < v_ra) (hvrb : 0 < v_rb) :
  (deriv (fun wa => wholesaleProfitA q s t c v_ra wa w_b) w_a = 0 ∧ deriv (fun wb => wholesaleProfitB q s t c v_rb w_a wb) w_b = 0) ↔ (w_a = wholesalePriceA q s t c v_ra v_rb ∧ w_b = wholesalePriceB q s t c v_ra v_rb) := by
  have hlt : ∀ v : ℝ, 0 < v → catchWholesale q v < 1 := fun v hv =>
    Real.rpow_lt_one hq.1.le hq.2 (by positivity)
  set ρa := catchWholesale q v_ra with hρa
  set ρb := catchWholesale q v_rb with hρb
  have ha1 : 0 < 1 - ρa := by have := hlt v_ra hvra; linarith
  have hb1 : 0 < 1 - ρb := by have := hlt v_rb hvrb; linarith
  have hka : kappa q s v_ra = s * ρa / (1 - ρa) := rfl
  have hkb : kappa q s v_rb = s * ρb / (1 - ρb) := rfl
  have hDA : HasDerivAt (fun x => wholesaleDemandA t x w_b) ((0 - 1) / (6 * t)) w_a :=
    (((hasDerivAt_const w_a w_b).sub (hasDerivAt_id w_a)).div_const (6 * t)).const_add (1 / 2)
  have hDB : HasDerivAt (fun x => wholesaleDemandB t w_a x) ((0 - 1) / (6 * t)) w_b :=
    (((hasDerivAt_const w_b w_a).sub (hasDerivAt_id w_b)).div_const (6 * t)).const_add (1 / 2)
  have hPA : HasDerivAt (fun wa => wholesaleProfitA q s t c v_ra wa w_b)
      ((1 - ρa) / (6 * t) * (3 * t + w_b + c + kappa q s v_ra - 2 * w_a)) w_a := by
    have h := ((((hasDerivAt_id w_a).sub_const c).const_mul (1 - ρa)).mul hDA).sub
      ((hDA.const_mul s).mul_const ρa)
    refine h.congr_deriv ?_
    rw [hka]
    simp only [wholesaleDemandA, id]
    field_simp
    ring
  have hPB : HasDerivAt (fun wb => wholesaleProfitB q s t c v_rb w_a wb)
      ((1 - ρb) / (6 * t) * (3 * t + w_a + c + kappa q s v_rb - 2 * w_b)) w_b := by
    have h := ((((hasDerivAt_id w_b).sub_const c).const_mul (1 - ρb)).mul hDB).sub
      ((hDB.const_mul s).mul_const ρb)
    refine h.congr_deriv ?_
    rw [hkb]
    simp only [wholesaleDemandB, id]
    field_simp
    ring
  rw [hPA.deriv, hPB.deriv]
  have hca : (1 - ρa) / (6 * t) ≠ 0 := by positivity
  have hcb : (1 - ρb) / (6 * t) ≠ 0 := by positivity
  rw [mul_eq_zero, mul_eq_zero]
  simp only [hca, hcb, false_or]
  unfold wholesalePriceA wholesalePriceB
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

end DrugMarket

open DrugMarket in
theorem solution (q s t c v_ra v_rb w_a w_b : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hs : 0 < s) (ht : 0 < t) (hvra : 0 < v_ra) (hvrb : 0 < v_rb) :
  (deriv (fun wa => wholesaleProfitA q s t c v_ra wa w_b) w_a = 0 ∧ deriv (fun wb => wholesaleProfitB q s t c v_rb w_a wb) w_b = 0) ↔ (w_a = wholesalePriceA q s t c v_ra v_rb ∧ w_b = wholesalePriceB q s t c v_ra v_rb) := by
  have hlt : ∀ v : ℝ, 0 < v → catchWholesale q v < 1 := fun v hv =>
    Real.rpow_lt_one hq.1.le hq.2 (by positivity)
  set ρa := catchWholesale q v_ra with hρa
  set ρb := catchWholesale q v_rb with hρb
  have ha1 : 0 < 1 - ρa := by have := hlt v_ra hvra; linarith
  have hb1 : 0 < 1 - ρb := by have := hlt v_rb hvrb; linarith
  have hka : kappa q s v_ra = s * ρa / (1 - ρa) := rfl
  have hkb : kappa q s v_rb = s * ρb / (1 - ρb) := rfl
  have hDA : HasDerivAt (fun x => wholesaleDemandA t x w_b) ((0 - 1) / (6 * t)) w_a :=
    (((hasDerivAt_const w_a w_b).sub (hasDerivAt_id w_a)).div_const (6 * t)).const_add (1 / 2)
  have hDB : HasDerivAt (fun x => wholesaleDemandB t w_a x) ((0 - 1) / (6 * t)) w_b :=
    (((hasDerivAt_const w_b w_a).sub (hasDerivAt_id w_b)).div_const (6 * t)).const_add (1 / 2)
  have hPA : HasDerivAt (fun wa => wholesaleProfitA q s t c v_ra wa w_b)
      ((1 - ρa) / (6 * t) * (3 * t + w_b + c + kappa q s v_ra - 2 * w_a)) w_a := by
    have h := ((((hasDerivAt_id w_a).sub_const c).const_mul (1 - ρa)).mul hDA).sub
      ((hDA.const_mul s).mul_const ρa)
    refine h.congr_deriv ?_
    rw [hka]
    simp only [wholesaleDemandA, id]
    field_simp
    ring
  have hPB : HasDerivAt (fun wb => wholesaleProfitB q s t c v_rb w_a wb)
      ((1 - ρb) / (6 * t) * (3 * t + w_a + c + kappa q s v_rb - 2 * w_b)) w_b := by
    have h := ((((hasDerivAt_id w_b).sub_const c).const_mul (1 - ρb)).mul hDB).sub
      ((hDB.const_mul s).mul_const ρb)
    refine h.congr_deriv ?_
    rw [hkb]
    simp only [wholesaleDemandB, id]
    field_simp
    ring
  rw [hPA.deriv, hPB.deriv]
  have hca : (1 - ρa) / (6 * t) ≠ 0 := by positivity
  have hcb : (1 - ρb) / (6 * t) ≠ 0 := by positivity
  rw [mul_eq_zero, mul_eq_zero]
  simp only [hca, hcb, false_or]
  unfold wholesalePriceA wholesalePriceB
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith
