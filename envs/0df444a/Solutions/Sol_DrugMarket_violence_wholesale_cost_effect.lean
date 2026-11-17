-- Prove2me | solution 1 for DrugMarket.violence_wholesale_cost_effect
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:31:12.622357+00:00
-- url     : https://prove2.me/submissions/6b42acce-ab7e-44e9-8b01-d06fe970d10c

import Mathlib
import Definitions.Def_drug_market_model
import Definitions.Def_drug_market_equilibrium
namespace DrugMarket
theorem violence_wholesale_cost_effect (q s t v_r w_a w_b : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hs : 0 < s) (ht : 0 < t) (hvr : 0 < v_r) (hmarg : 0 < t + (w_b - w_a)/3) :
  deriv (fun wa => grossProfitA t wa w_b) w_a < 0 ∧ deriv (fun wa => violenceBR q s v_r (grossProfitA t wa w_b)) w_a = qHat q s v_r (grossProfitA t w_a w_b) * deriv (fun wa => grossProfitA t wa w_b) w_a ∧ deriv (fun wa => violenceBR q s v_r (grossProfitA t wa w_b)) w_a < 0 ∧ deriv (fun wb => violenceBR q s v_r (grossProfitA t w_a wb)) w_b > 0 ∧ deriv (fun wa => violenceBR q s v_r (grossProfitA t wa w_b)) w_a + deriv (fun wb => violenceBR q s v_r (grossProfitA t w_a wb)) w_b = 0 := by
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
  have hmA := hmarg
  have hGa : HasDerivAt (fun wa => grossProfitA t wa w_b) (-(t + (w_b - w_a) / 3) / (3 * t)) w_a := by
    have := ((((hasDerivAt_const w_a w_b).sub (hasDerivAt_id w_a)).div_const 3).const_add t).pow 2
      |>.div_const (2 * t)
    refine this.congr_deriv ?_
    (try norm_num) <;> field_simp <;> ring
  have hGb : HasDerivAt (fun wb => grossProfitA t w_a wb) ((t + (w_b - w_a) / 3) / (3 * t)) w_b := by
    have := ((((hasDerivAt_id w_b).sub (hasDerivAt_const w_b w_a)).div_const 3).const_add t).pow 2
      |>.div_const (2 * t)
    refine this.congr_deriv ?_
    (try norm_num) <;> field_simp <;> ring
  have hg0 : 0 ≤ grossProfitA t w_a w_b := by unfold grossProfitA; positivity
  have hqp : 0 < qHat q s v_r (grossProfitA t w_a w_b) := by
    unfold qHat
    exact div_pos_of_neg_of_neg (by linarith) (mul_neg_of_neg_of_pos hL (by linarith))
  have hcA : HasDerivAt (fun wa => violenceBR q s v_r (grossProfitA t wa w_b))
      (qHat q s v_r (grossProfitA t w_a w_b) * (-(t + (w_b - w_a) / 3) / (3 * t))) w_a :=
    by have h := (hV (grossProfitA t w_a w_b) hg0).comp w_a hGa; exact h
  have hcB : HasDerivAt (fun wb => violenceBR q s v_r (grossProfitA t w_a wb))
      (qHat q s v_r (grossProfitA t w_a w_b) * ((t + (w_b - w_a) / 3) / (3 * t))) w_b :=
    by have h := (hV (grossProfitA t w_a w_b) hg0).comp w_b hGb; exact h
  have hdA : -(t + (w_b - w_a) / 3) / (3 * t) < 0 := div_neg_of_neg_of_pos (by linarith) (by positivity)
  have hdB : 0 < (t + (w_b - w_a) / 3) / (3 * t) := div_pos hmarg (by positivity)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hGa.deriv]; exact hdA
  · rw [hcA.deriv, hGa.deriv]
  · rw [hcA.deriv]; exact mul_neg_of_pos_of_neg hqp hdA
  · rw [hcB.deriv]; exact mul_pos hqp hdB
  · rw [hcA.deriv, hcB.deriv]; ring

end DrugMarket

open DrugMarket in
theorem solution (q s t v_r w_a w_b : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hs : 0 < s) (ht : 0 < t) (hvr : 0 < v_r) (hmarg : 0 < t + (w_b - w_a)/3) :
  deriv (fun wa => grossProfitA t wa w_b) w_a < 0 ∧ deriv (fun wa => violenceBR q s v_r (grossProfitA t wa w_b)) w_a = qHat q s v_r (grossProfitA t w_a w_b) * deriv (fun wa => grossProfitA t wa w_b) w_a ∧ deriv (fun wa => violenceBR q s v_r (grossProfitA t wa w_b)) w_a < 0 ∧ deriv (fun wb => violenceBR q s v_r (grossProfitA t w_a wb)) w_b > 0 ∧ deriv (fun wa => violenceBR q s v_r (grossProfitA t wa w_b)) w_a + deriv (fun wb => violenceBR q s v_r (grossProfitA t w_a wb)) w_b = 0 := by
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
  have hmA := hmarg
  have hGa : HasDerivAt (fun wa => grossProfitA t wa w_b) (-(t + (w_b - w_a) / 3) / (3 * t)) w_a := by
    have := ((((hasDerivAt_const w_a w_b).sub (hasDerivAt_id w_a)).div_const 3).const_add t).pow 2
      |>.div_const (2 * t)
    refine this.congr_deriv ?_
    (try norm_num) <;> field_simp <;> ring
  have hGb : HasDerivAt (fun wb => grossProfitA t w_a wb) ((t + (w_b - w_a) / 3) / (3 * t)) w_b := by
    have := ((((hasDerivAt_id w_b).sub (hasDerivAt_const w_b w_a)).div_const 3).const_add t).pow 2
      |>.div_const (2 * t)
    refine this.congr_deriv ?_
    (try norm_num) <;> field_simp <;> ring
  have hg0 : 0 ≤ grossProfitA t w_a w_b := by unfold grossProfitA; positivity
  have hqp : 0 < qHat q s v_r (grossProfitA t w_a w_b) := by
    unfold qHat
    exact div_pos_of_neg_of_neg (by linarith) (mul_neg_of_neg_of_pos hL (by linarith))
  have hcA : HasDerivAt (fun wa => violenceBR q s v_r (grossProfitA t wa w_b))
      (qHat q s v_r (grossProfitA t w_a w_b) * (-(t + (w_b - w_a) / 3) / (3 * t))) w_a :=
    by have h := (hV (grossProfitA t w_a w_b) hg0).comp w_a hGa; exact h
  have hcB : HasDerivAt (fun wb => violenceBR q s v_r (grossProfitA t w_a wb))
      (qHat q s v_r (grossProfitA t w_a w_b) * ((t + (w_b - w_a) / 3) / (3 * t))) w_b :=
    by have h := (hV (grossProfitA t w_a w_b) hg0).comp w_b hGb; exact h
  have hdA : -(t + (w_b - w_a) / 3) / (3 * t) < 0 := div_neg_of_neg_of_pos (by linarith) (by positivity)
  have hdB : 0 < (t + (w_b - w_a) / 3) / (3 * t) := div_pos hmarg (by positivity)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hGa.deriv]; exact hdA
  · rw [hcA.deriv, hGa.deriv]
  · rw [hcA.deriv]; exact mul_neg_of_pos_of_neg hqp hdA
  · rw [hcB.deriv]; exact mul_pos hqp hdB
  · rw [hcA.deriv, hcB.deriv]; ring
