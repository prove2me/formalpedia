-- Prove2me | solution 1 for DrugMarket.violence_effectiveness_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:34:48.916697+00:00
-- url     : https://prove2.me/submissions/0bcbfe07-80cc-43d4-be80-3bf9b84a4894

import Mathlib
import Definitions.Def_drug_market_model
import Definitions.Def_drug_market_equilibrium
namespace DrugMarket
theorem violence_effectiveness_cutoff (q s v_r g : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hs : 0 < s) (hvr : 0 < v_r) (hg : 0 ≤ g) :
  deriv (fun qq => violenceBR qq s v_r g) q = -(v_r * (1 + Real.log (qHat q s v_r g))) / (q * (Real.log q)^2) ∧ (deriv (fun qq => violenceBR qq s v_r g) q > 0 ↔ Real.log (qHat q s v_r g) < -1) ∧ (deriv (fun qq => violenceBR qq s v_r g) q < 0 ↔ -1 < Real.log (qHat q s v_r g)) ∧ (deriv (fun qq => violenceBR qq s v_r g) q = 0 ↔ Real.log (qHat q s v_r g) = -1) := by
  have hq0 : 0 < q := hq.1
  have hL : Real.log q < 0 := Real.log_neg hq.1 hq.2
  have hLne : Real.log q ≠ 0 := hL.ne
  have hgs : 0 < g + s := by linarith
  have hK : Real.log q * (g + s) ≠ 0 := mul_ne_zero hLne hgs.ne'
  have hqp : 0 < qHat q s v_r g := by
    unfold qHat
    exact div_pos_of_neg_of_neg (by linarith) (mul_neg_of_neg_of_pos hL hgs)
  have hlog := Real.hasDerivAt_log hq0.ne'
  have hQ := (hasDerivAt_const q (-v_r)).div (hlog.mul_const (g + s)) hK
  have h2 := ((hQ.log hqp.ne').const_mul v_r).div hlog hLne
  have hd : HasDerivAt (fun qq => violenceBR qq s v_r g)
      (-(v_r * (1 + Real.log (qHat q s v_r g))) / (q * (Real.log q) ^ 2)) q := by
    refine h2.congr_deriv ?_
    have e : -v_r / (Real.log q * (g + s)) = qHat q s v_r g := rfl
    try simp only [Pi.div_apply, Pi.mul_apply]
    rw [show qHat q s v_r g = -v_r / (Real.log q * (g + s)) from rfl]
    field_simp
    ring
  rw [hd.deriv]
  set Lh := Real.log (qHat q s v_r g)
  have hc : 0 < v_r / (q * (Real.log q) ^ 2) := by positivity
  have key : -(v_r * (1 + Lh)) / (q * (Real.log q) ^ 2) = -(v_r / (q * (Real.log q) ^ 2)) * (1 + Lh) := by ring
  rw [key]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · constructor <;> intro h <;> nlinarith
  · constructor <;> intro h <;> nlinarith
  · constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · linarith
      · linarith
    · intro h; rw [h]; ring

end DrugMarket

open DrugMarket in
theorem solution (q s v_r g : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hs : 0 < s) (hvr : 0 < v_r) (hg : 0 ≤ g) :
  deriv (fun qq => violenceBR qq s v_r g) q = -(v_r * (1 + Real.log (qHat q s v_r g))) / (q * (Real.log q)^2) ∧ (deriv (fun qq => violenceBR qq s v_r g) q > 0 ↔ Real.log (qHat q s v_r g) < -1) ∧ (deriv (fun qq => violenceBR qq s v_r g) q < 0 ↔ -1 < Real.log (qHat q s v_r g)) ∧ (deriv (fun qq => violenceBR qq s v_r g) q = 0 ↔ Real.log (qHat q s v_r g) = -1) := by
  have hq0 : 0 < q := hq.1
  have hL : Real.log q < 0 := Real.log_neg hq.1 hq.2
  have hLne : Real.log q ≠ 0 := hL.ne
  have hgs : 0 < g + s := by linarith
  have hK : Real.log q * (g + s) ≠ 0 := mul_ne_zero hLne hgs.ne'
  have hqp : 0 < qHat q s v_r g := by
    unfold qHat
    exact div_pos_of_neg_of_neg (by linarith) (mul_neg_of_neg_of_pos hL hgs)
  have hlog := Real.hasDerivAt_log hq0.ne'
  have hQ := (hasDerivAt_const q (-v_r)).div (hlog.mul_const (g + s)) hK
  have h2 := ((hQ.log hqp.ne').const_mul v_r).div hlog hLne
  have hd : HasDerivAt (fun qq => violenceBR qq s v_r g)
      (-(v_r * (1 + Real.log (qHat q s v_r g))) / (q * (Real.log q) ^ 2)) q := by
    refine h2.congr_deriv ?_
    have e : -v_r / (Real.log q * (g + s)) = qHat q s v_r g := rfl
    try simp only [Pi.div_apply, Pi.mul_apply]
    rw [show qHat q s v_r g = -v_r / (Real.log q * (g + s)) from rfl]
    field_simp
    ring
  rw [hd.deriv]
  set Lh := Real.log (qHat q s v_r g)
  have hc : 0 < v_r / (q * (Real.log q) ^ 2) := by positivity
  have key : -(v_r * (1 + Lh)) / (q * (Real.log q) ^ 2) = -(v_r / (q * (Real.log q) ^ 2)) * (1 + Lh) := by ring
  rw [key]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · constructor <;> intro h <;> nlinarith
  · constructor <;> intro h <;> nlinarith
  · constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · linarith
      · linarith
    · intro h; rw [h]; ring
