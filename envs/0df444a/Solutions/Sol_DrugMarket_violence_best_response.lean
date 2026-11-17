-- Prove2me | solution 1 for DrugMarket.violence_best_response
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:36:16.23614+00:00
-- url     : https://prove2.me/submissions/6c0be231-f9cb-447b-b38a-44f8e055572a

import Mathlib
import Definitions.Def_drug_market_model
import Definitions.Def_drug_market_equilibrium
namespace DrugMarket
theorem violence_best_response (q s v_r g : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hs : 0 < s) (hvr : 0 < v_r) (hg : 0 ≤ g) :
  (qHat q s v_r g < 1 → ∀ v ∈ Set.Ici (0:ℝ), retailViolenceObjective q s v_r g v ≤ retailViolenceObjective q s v_r g (violenceBR q s v_r g) ∧ (retailViolenceObjective q s v_r g v = retailViolenceObjective q s v_r g (violenceBR q s v_r g) ↔ v = violenceBR q s v_r g)) ∧ (1 ≤ qHat q s v_r g → ∀ v ∈ Set.Ici (0:ℝ), retailViolenceObjective q s v_r g v ≤ retailViolenceObjective q s v_r g 0 ∧ (retailViolenceObjective q s v_r g v = retailViolenceObjective q s v_r g 0 ↔ v = 0)) := by
  have hq0 : 0 < q := hq.1
  have hL : Real.log q < 0 := Real.log_neg hq.1 hq.2
  have hLne : Real.log q ≠ 0 := hL.ne
  have hgs : 0 < g + s := by linarith
  have hvrne : v_r ≠ 0 := hvr.ne'
  have hcatch : ∀ v, catchRetail q v_r v = Real.exp (Real.log q * (v / v_r)) := by
    intro v
    show q ^ (v / v_r) = _
    exact Real.rpow_def_of_pos hq0 _
  have hO : ∀ v, retailViolenceObjective q s v_r g v =
      g - (g + s) * Real.exp (Real.log q * (v / v_r)) - v := by
    intro v; unfold retailViolenceObjective; rw [hcatch]; ring
  set Q := qHat q s v_r g with hQdef
  have hQ : Q = -v_r / (Real.log q * (g + s)) := rfl
  have hQpos : 0 < Q := by
    rw [hQ]; exact div_pos_of_neg_of_neg (by linarith) (mul_neg_of_neg_of_pos hL hgs)
  have hKQ : (g + s) * Q = -v_r / Real.log q := by rw [hQ]; field_simp
  have hKQpos : 0 < (g + s) * Q := mul_pos hgs hQpos
  have hvx : ∀ v, v = -((g + s) * Q) * (Real.log q * (v / v_r)) := by
    intro v; rw [hKQ]; field_simp
  refine ⟨fun _ v _ => ?_, fun hQ1 v hv => ?_⟩
  · set vs := violenceBR q s v_r g with hvs
    have hxs : Real.log q * (vs / v_r) = Real.log Q := by
      rw [hvs]; unfold violenceBR; rw [← hQdef]; field_simp
    have hOvs : retailViolenceObjective q s v_r g vs = g - (g + s) * Q - vs := by
      rw [hO, hxs, Real.exp_log hQpos]
    set t := Real.log q * (v / v_r) - Real.log Q with ht
    have hex : Real.exp (Real.log q * (v / v_r)) = Q * Real.exp t := by
      have : Real.log q * (v / v_r) = Real.log Q + t := by rw [ht]; ring
      rw [this, Real.exp_add, Real.exp_log hQpos]
    have hv2 : v - vs = -((g + s) * Q) * t := by
      have h1 := hvx v
      have h2 := hvx vs
      rw [hxs] at h2
      rw [ht]
      linear_combination h1 - h2
    have hdiff : retailViolenceObjective q s v_r g vs - retailViolenceObjective q s v_r g v =
        (g + s) * Q * (Real.exp t - 1 - t) := by
      rw [hO v, hex, hOvs]
      linear_combination hv2
    have hE := Real.add_one_le_exp t
    refine ⟨?_, ?_⟩
    · have : 0 ≤ (g + s) * Q * (Real.exp t - 1 - t) := mul_nonneg hKQpos.le (by linarith)
      linarith
    · constructor
      · intro h
        have h0 : (g + s) * Q * (Real.exp t - 1 - t) = 0 := by rw [← hdiff, h]; ring
        have h3 : Real.exp t - 1 - t = 0 := by
          rcases mul_eq_zero.mp h0 with h | h
          · exact absurd h hKQpos.ne'
          · exact h
        have htz : t = 0 := by
          by_contra hne
          have := Real.add_one_lt_exp hne
          linarith
        have : v - vs = 0 := by rw [hv2, htz]; ring
        linarith
      · intro h; rw [h]
  · have hv0 : (0:ℝ) ≤ v := hv
    set x := Real.log q * (v / v_r) with hx
    have hxle : x ≤ 0 := by
      rw [hx]; exact mul_nonpos_of_nonpos_of_nonneg hL.le (div_nonneg hv0 hvr.le)
    have hO0 : retailViolenceObjective q s v_r g 0 = g - (g + s) := by
      rw [hO]; simp
    have hv2 := hvx v
    rw [← hx] at hv2
    have hE := Real.add_one_le_exp x
    have hdiff : retailViolenceObjective q s v_r g 0 - retailViolenceObjective q s v_r g v =
        (g + s) * (Real.exp x - 1 - x) + (g + s) * ((1 - Q) * x) := by
      rw [hO v, hO0, ← hx]
      linear_combination hv2
    have hA : 0 ≤ (g + s) * (Real.exp x - 1 - x) := mul_nonneg hgs.le (by linarith)
    have hB : 0 ≤ (g + s) * ((1 - Q) * x) :=
      mul_nonneg hgs.le (mul_nonneg_of_nonpos_of_nonpos (by linarith) hxle)
    refine ⟨by linarith, ?_⟩
    constructor
    · intro h
      have h0 : (g + s) * (Real.exp x - 1 - x) = 0 := by linarith
      have h3 : Real.exp x - 1 - x = 0 := by
        rcases mul_eq_zero.mp h0 with h | h
        · exact absurd h hgs.ne'
        · exact h
      have hxz : x = 0 := by
        by_contra hne
        have := Real.add_one_lt_exp hne
        linarith
      rw [hv2, hxz]; ring
    · intro h; rw [h]

end DrugMarket

open DrugMarket in
theorem solution (q s v_r g : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (hs : 0 < s) (hvr : 0 < v_r) (hg : 0 ≤ g) :
  (qHat q s v_r g < 1 → ∀ v ∈ Set.Ici (0:ℝ), retailViolenceObjective q s v_r g v ≤ retailViolenceObjective q s v_r g (violenceBR q s v_r g) ∧ (retailViolenceObjective q s v_r g v = retailViolenceObjective q s v_r g (violenceBR q s v_r g) ↔ v = violenceBR q s v_r g)) ∧ (1 ≤ qHat q s v_r g → ∀ v ∈ Set.Ici (0:ℝ), retailViolenceObjective q s v_r g v ≤ retailViolenceObjective q s v_r g 0 ∧ (retailViolenceObjective q s v_r g v = retailViolenceObjective q s v_r g 0 ↔ v = 0)) := by
  have hq0 : 0 < q := hq.1
  have hL : Real.log q < 0 := Real.log_neg hq.1 hq.2
  have hLne : Real.log q ≠ 0 := hL.ne
  have hgs : 0 < g + s := by linarith
  have hvrne : v_r ≠ 0 := hvr.ne'
  have hcatch : ∀ v, catchRetail q v_r v = Real.exp (Real.log q * (v / v_r)) := by
    intro v
    show q ^ (v / v_r) = _
    exact Real.rpow_def_of_pos hq0 _
  have hO : ∀ v, retailViolenceObjective q s v_r g v =
      g - (g + s) * Real.exp (Real.log q * (v / v_r)) - v := by
    intro v; unfold retailViolenceObjective; rw [hcatch]; ring
  set Q := qHat q s v_r g with hQdef
  have hQ : Q = -v_r / (Real.log q * (g + s)) := rfl
  have hQpos : 0 < Q := by
    rw [hQ]; exact div_pos_of_neg_of_neg (by linarith) (mul_neg_of_neg_of_pos hL hgs)
  have hKQ : (g + s) * Q = -v_r / Real.log q := by rw [hQ]; field_simp
  have hKQpos : 0 < (g + s) * Q := mul_pos hgs hQpos
  have hvx : ∀ v, v = -((g + s) * Q) * (Real.log q * (v / v_r)) := by
    intro v; rw [hKQ]; field_simp
  refine ⟨fun _ v _ => ?_, fun hQ1 v hv => ?_⟩
  · set vs := violenceBR q s v_r g with hvs
    have hxs : Real.log q * (vs / v_r) = Real.log Q := by
      rw [hvs]; unfold violenceBR; rw [← hQdef]; field_simp
    have hOvs : retailViolenceObjective q s v_r g vs = g - (g + s) * Q - vs := by
      rw [hO, hxs, Real.exp_log hQpos]
    set t := Real.log q * (v / v_r) - Real.log Q with ht
    have hex : Real.exp (Real.log q * (v / v_r)) = Q * Real.exp t := by
      have : Real.log q * (v / v_r) = Real.log Q + t := by rw [ht]; ring
      rw [this, Real.exp_add, Real.exp_log hQpos]
    have hv2 : v - vs = -((g + s) * Q) * t := by
      have h1 := hvx v
      have h2 := hvx vs
      rw [hxs] at h2
      rw [ht]
      linear_combination h1 - h2
    have hdiff : retailViolenceObjective q s v_r g vs - retailViolenceObjective q s v_r g v =
        (g + s) * Q * (Real.exp t - 1 - t) := by
      rw [hO v, hex, hOvs]
      linear_combination hv2
    have hE := Real.add_one_le_exp t
    refine ⟨?_, ?_⟩
    · have : 0 ≤ (g + s) * Q * (Real.exp t - 1 - t) := mul_nonneg hKQpos.le (by linarith)
      linarith
    · constructor
      · intro h
        have h0 : (g + s) * Q * (Real.exp t - 1 - t) = 0 := by rw [← hdiff, h]; ring
        have h3 : Real.exp t - 1 - t = 0 := by
          rcases mul_eq_zero.mp h0 with h | h
          · exact absurd h hKQpos.ne'
          · exact h
        have htz : t = 0 := by
          by_contra hne
          have := Real.add_one_lt_exp hne
          linarith
        have : v - vs = 0 := by rw [hv2, htz]; ring
        linarith
      · intro h; rw [h]
  · have hv0 : (0:ℝ) ≤ v := hv
    set x := Real.log q * (v / v_r) with hx
    have hxle : x ≤ 0 := by
      rw [hx]; exact mul_nonpos_of_nonpos_of_nonneg hL.le (div_nonneg hv0 hvr.le)
    have hO0 : retailViolenceObjective q s v_r g 0 = g - (g + s) := by
      rw [hO]; simp
    have hv2 := hvx v
    rw [← hx] at hv2
    have hE := Real.add_one_le_exp x
    have hdiff : retailViolenceObjective q s v_r g 0 - retailViolenceObjective q s v_r g v =
        (g + s) * (Real.exp x - 1 - x) + (g + s) * ((1 - Q) * x) := by
      rw [hO v, hO0, ← hx]
      linear_combination hv2
    have hA : 0 ≤ (g + s) * (Real.exp x - 1 - x) := mul_nonneg hgs.le (by linarith)
    have hB : 0 ≤ (g + s) * ((1 - Q) * x) :=
      mul_nonneg hgs.le (mul_nonneg_of_nonpos_of_nonpos (by linarith) hxle)
    refine ⟨by linarith, ?_⟩
    constructor
    · intro h
      have h0 : (g + s) * (Real.exp x - 1 - x) = 0 := by linarith
      have h3 : Real.exp x - 1 - x = 0 := by
        rcases mul_eq_zero.mp h0 with h | h
        · exact absurd h hgs.ne'
        · exact h
      have hxz : x = 0 := by
        by_contra hne
        have := Real.add_one_lt_exp hne
        linarith
      rw [hv2, hxz]; ring
    · intro h; rw [h]
