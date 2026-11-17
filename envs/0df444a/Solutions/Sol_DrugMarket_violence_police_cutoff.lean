-- Prove2me | solution 1 for DrugMarket.violence_police_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:34:18.36567+00:00
-- url     : https://prove2.me/submissions/ff2e8ef1-76bd-4e11-b5b3-c295a840398b

import Mathlib
import Definitions.Def_drug_market_model
import Definitions.Def_drug_market_equilibrium
namespace DrugMarket
theorem violence_police_cutoff (q s v_r g : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hs : 0 < s) (hvr : 0 < v_r) (hg : 0 ≤ g) :
  deriv (fun vr => violenceBR q s vr g) v_r = (1 + Real.log (qHat q s v_r g)) / Real.log q ∧ (deriv (fun vr => violenceBR q s vr g) v_r > 0 ↔ Real.log (qHat q s v_r g) < -1) ∧ (deriv (fun vr => violenceBR q s vr g) v_r < 0 ↔ -1 < Real.log (qHat q s v_r g)) ∧ (deriv (fun vr => violenceBR q s vr g) v_r = 0 ↔ Real.log (qHat q s v_r g) = -1) := by
  have hL : Real.log q < 0 := Real.log_neg hq.1 hq.2
  have hLne : Real.log q ≠ 0 := hL.ne
  have hgs : 0 < g + s := by linarith
  have hK : Real.log q * (g + s) ≠ 0 := mul_ne_zero hLne hgs.ne'
  have hqp : 0 < qHat q s v_r g := by
    unfold qHat
    exact div_pos_of_neg_of_neg (by linarith) (mul_neg_of_neg_of_pos hL hgs)
  have hQ : HasDerivAt (fun vr => -vr / (Real.log q * (g + s))) (-1 / (Real.log q * (g + s))) v_r := by
    simpa using ((hasDerivAt_id v_r).neg).div_const (Real.log q * (g + s))
  have h2 := ((hasDerivAt_id v_r).mul (hQ.log hqp.ne')).div_const (Real.log q)
  have hd : HasDerivAt (fun vr => violenceBR q s vr g)
      ((1 + Real.log (qHat q s v_r g)) / Real.log q) v_r := by
    refine h2.congr_deriv ?_
    have e : -v_r / (Real.log q * (g + s)) = qHat q s v_r g := rfl
    simp only [id, e]
    congr 1
    rw [show qHat q s v_r g = -v_r / (Real.log q * (g + s)) from rfl]
    field_simp
    ring
  rw [hd.deriv]
  set Lh := Real.log (qHat q s v_r g)
  have hc : 0 < -(1 / Real.log q) := by
    have : 1 / Real.log q < 0 := one_div_neg.mpr hL
    linarith
  have key : (1 + Lh) / Real.log q = -(-(1 / Real.log q)) * (1 + Lh) := by ring
  rw [key]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · constructor <;> intro h <;> nlinarith
  · constructor <;> intro h <;> nlinarith
  · constructor
    · intro h
      have := mul_eq_zero.mp h
      rcases this with h | h
      · linarith
      · linarith
    · intro h; rw [h]; ring

end DrugMarket

open DrugMarket in
theorem solution (q s v_r g : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hs : 0 < s) (hvr : 0 < v_r) (hg : 0 ≤ g) :
  deriv (fun vr => violenceBR q s vr g) v_r = (1 + Real.log (qHat q s v_r g)) / Real.log q ∧ (deriv (fun vr => violenceBR q s vr g) v_r > 0 ↔ Real.log (qHat q s v_r g) < -1) ∧ (deriv (fun vr => violenceBR q s vr g) v_r < 0 ↔ -1 < Real.log (qHat q s v_r g)) ∧ (deriv (fun vr => violenceBR q s vr g) v_r = 0 ↔ Real.log (qHat q s v_r g) = -1) := by
  have hL : Real.log q < 0 := Real.log_neg hq.1 hq.2
  have hLne : Real.log q ≠ 0 := hL.ne
  have hgs : 0 < g + s := by linarith
  have hK : Real.log q * (g + s) ≠ 0 := mul_ne_zero hLne hgs.ne'
  have hqp : 0 < qHat q s v_r g := by
    unfold qHat
    exact div_pos_of_neg_of_neg (by linarith) (mul_neg_of_neg_of_pos hL hgs)
  have hQ : HasDerivAt (fun vr => -vr / (Real.log q * (g + s))) (-1 / (Real.log q * (g + s))) v_r := by
    simpa using ((hasDerivAt_id v_r).neg).div_const (Real.log q * (g + s))
  have h2 := ((hasDerivAt_id v_r).mul (hQ.log hqp.ne')).div_const (Real.log q)
  have hd : HasDerivAt (fun vr => violenceBR q s vr g)
      ((1 + Real.log (qHat q s v_r g)) / Real.log q) v_r := by
    refine h2.congr_deriv ?_
    have e : -v_r / (Real.log q * (g + s)) = qHat q s v_r g := rfl
    simp only [id, e]
    congr 1
    rw [show qHat q s v_r g = -v_r / (Real.log q * (g + s)) from rfl]
    field_simp
    ring
  rw [hd.deriv]
  set Lh := Real.log (qHat q s v_r g)
  have hc : 0 < -(1 / Real.log q) := by
    have : 1 / Real.log q < 0 := one_div_neg.mpr hL
    linarith
  have key : (1 + Lh) / Real.log q = -(-(1 / Real.log q)) * (1 + Lh) := by ring
  rw [key]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · constructor <;> intro h <;> nlinarith
  · constructor <;> intro h <;> nlinarith
  · constructor
    · intro h
      have := mul_eq_zero.mp h
      rcases this with h | h
      · linarith
      · linarith
    · intro h; rw [h]; ring
