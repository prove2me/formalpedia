-- Prove2me | solution 1 for FlexLearning.Threshold.break_even_cost
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T10:45:01.459056+00:00
-- url     : https://prove2.me/submissions/2d570662-a24f-4569-80fc-ab8ae84b0e90

import Mathlib
import Definitions.Def_FlexLearning_Threshold_Model
import Theorems.Thm_FlexLearning_Threshold_piBarN_eq

open FlexLearning.Threshold MeasureTheory

namespace FlexLAuxB

noncomputable def ps (r : ℝ) : ℝ := (max r 0) ^ 2 / 2
noncomputable def Ps (r : ℝ) : ℝ := (max r 0) ^ 3 / 6

lemma ps_cont : Continuous ps := by
  unfold ps; fun_prop

lemma prior_integral (x U : ℝ) (hU : 0 < U) (f : ℝ → ℝ) :
    ∫ d, f d ∂(prior x U) = U⁻¹ * ∫ d in x..x + U, f d := by
  unfold prior
  rw [integral_smul_measure, intervalIntegral.integral_of_le (by linarith),
    integral_Icc_eq_integral_Ioc]
  simp [ENNReal.toReal_inv, ENNReal.toReal_ofReal hU.le]

lemma int_min (x U Q : ℝ) (hU : 0 < U) :
    ∫ d in x..x + U, min d Q =
      if Q ≤ x then Q * U
      else if Q ≤ x + U then x * U + (Q - x) * U - (Q - x) ^ 2 / 2
      else x * U + U ^ 2 / 2 := by
  split_ifs with h1 h2
  · rw [intervalIntegral.integral_congr (g := fun _ => Q)]
    · simp; ring
    · intro d hd
      rw [Set.uIcc_of_le (by linarith)] at hd
      simp only
      exact min_eq_right (by linarith [hd.1])
  · have hc : Continuous fun d : ℝ => min d Q := continuous_id.min continuous_const
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := Q)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_congr (g := fun d => d) (a := x) (b := Q),
      intervalIntegral.integral_congr (g := fun _ => Q) (a := Q) (b := x + U)]
    · simp [integral_id]; ring
    · intro d hd
      rw [Set.uIcc_of_le h2] at hd
      exact min_eq_right hd.1
    · intro d hd
      rw [Set.uIcc_of_le (by linarith)] at hd
      exact min_eq_left hd.2
  · rw [intervalIntegral.integral_congr (g := fun d => d)]
    · simp [integral_id]; ring
    · intro d hd
      rw [Set.uIcc_of_le (by linarith)] at hd
      exact min_eq_left (by linarith [hd.2])

lemma int_min' (x U Q : ℝ) (hU : 0 < U) :
    ∫ d in x..x + U, min d Q = x * U + U ^ 2 / 2 - ps (x + U - Q) + ps (x - Q) := by
  rw [int_min x U Q hU]
  unfold ps
  split_ifs with h1 h2
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  · rw [max_eq_right (by linarith), max_eq_right (by linarith)]; ring

lemma int_ps (α β : ℝ) (h : α ≤ β) : ∫ r in α..β, ps r = Ps β - Ps α := by
  unfold ps Ps
  rcases le_total β 0 with hb | hb
  · rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
    · rw [max_eq_right hb, max_eq_right (by linarith)]; simp
    · intro r hr
      rw [Set.uIcc_of_le h] at hr
      simp only; rw [max_eq_right (by linarith [hr.2])]; ring
  rcases le_total 0 α with ha | ha
  · rw [intervalIntegral.integral_congr (g := fun r => r ^ 2 / 2)]
    · rw [max_eq_left hb, max_eq_left ha, intervalIntegral.integral_div, integral_pow]; ring
    · intro r hr
      rw [Set.uIcc_of_le h] at hr
      simp only; rw [max_eq_left (by linarith [hr.1])]
  · have hc : Continuous fun r : ℝ => (max r 0) ^ 2 / 2 := by fun_prop
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (a := α) (b := 0),
      intervalIntegral.integral_congr (g := fun r => r ^ 2 / 2) (a := 0) (b := β)]
    · rw [max_eq_left hb, max_eq_right ha, intervalIntegral.integral_div, integral_pow]
      simp; ring
    · intro r hr
      rw [Set.uIcc_of_le hb] at hr
      simp only; rw [max_eq_left hr.1]
    · intro r hr
      rw [Set.uIcc_of_le ha] at hr
      simp only; rw [max_eq_right hr.2]; ring

lemma int_ps_shift (α β k : ℝ) (h : α ≤ β) :
    ∫ r in α..β, ps (r + k) = Ps (β + k) - Ps (α + k) := by
  rw [intervalIntegral.integral_comp_add_right ps k, int_ps _ _ (by linarith)]

lemma prior_prob (x U : ℝ) (hU : 0 < U) : IsProbabilityMeasure (prior x U) := by
  constructor
  unfold prior
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Icc, smul_eq_mul]
  have : ENNReal.ofReal (x + U - x) = ENNReal.ofReal U := by congr 1; ring
  rw [this, ENNReal.inv_mul_cancel (by simp [hU]) ENNReal.ofReal_ne_top]

lemma prior2_integrable (x U : ℝ) (hU : 0 < U) (F : ℝ × ℝ → ℝ) (hF : Continuous F) :
    Integrable F (prior2 x U) := by
  unfold prior2 prior
  rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.prod_restrict,
    ← Measure.volume_eq_prod]
  exact ((hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).smul_measure
    (by simp [hU])).smul_measure (by simp [hU])

lemma sales_eq (Q a b : ℝ) (hb : 0 ≤ b) :
    salesF1 Q (a, b) + salesF2 Q (a, b) = min (a + b) Q := by
  unfold salesF1 salesF2
  simp only
  rcases le_total a Q with h | h
  · rw [min_eq_left h]
    rcases le_total b (Q - a) with h' | h'
    · rw [min_eq_left h', min_eq_left (by linarith)]
    · rw [min_eq_right h', min_eq_right (by linarith)]; ring
  · rw [min_eq_right h, sub_self, min_eq_right hb, min_eq_right (by linarith)]; ring

lemma inner_eq (x U Q a : ℝ) (hx : 0 ≤ x) (hU : 0 < U) (p : ℝ) :
    ∫ b, (p * salesF1 Q (a, b) + p * salesF2 Q (a, b)) ∂(prior x U) =
      p * (a + x + U / 2 - (ps (a + (x + U - Q)) - ps (a + (x - Q))) / U) := by
  rw [prior_integral x U hU]
  rw [intervalIntegral.integral_congr (g := fun b => p * a + p * min b (Q - a))]
  · rw [intervalIntegral.integral_add (f := fun _ => p * a) (g := fun b => p * min b (Q - a))
      intervalIntegrable_const
      (Continuous.intervalIntegrable (by fun_prop) _ _),
      intervalIntegral.integral_const_mul p (fun b => min b (Q - a)), int_min' x U (Q - a) hU]
    have e1 : x + U - (Q - a) = a + (x + U - Q) := by ring
    have e2 : x - (Q - a) = a + (x - Q) := by ring
    rw [e1, e2]
    simp
    field_simp
    ring
  · intro b hb
    rw [Set.uIcc_of_le (by linarith)] at hb
    simp only
    rw [← mul_add, sales_eq Q a b (by linarith [hb.1])]
    rw [← mul_add]
    congr 1
    rcases le_total (a + b) Q with h | h
    · rw [min_eq_left h, min_eq_left (by linarith)]
    · rw [min_eq_right h, min_eq_right (by linarith)]; ring

lemma piF_formula (p x U cF Q : ℝ) (hx : 0 ≤ x) (hU : 0 < U) :
    piF p x U cF Q = p * (2 * x + U -
      (Ps (2 * x + 2 * U - Q) - 2 * Ps (2 * x + U - Q) + Ps (2 * x - Q)) / U ^ 2) - cF * Q := by
  unfold piF
  have := prior_prob x U hU
  have hF : Continuous fun d : ℝ × ℝ => p * salesF1 Q d + p * salesF2 Q d := by
    unfold salesF1 salesF2; fun_prop
  rw [prior2, integral_prod _ (by simpa [prior2] using prior2_integrable x U hU _ hF)]
  simp_rw [inner_eq x U Q _ hx hU p]
  rw [prior_integral x U hU]
  have hc1 : Continuous fun a : ℝ => ps (a + (x + U - Q)) := ps_cont.comp (by fun_prop)
  have hc2 : Continuous fun a : ℝ => ps (a + (x - Q)) := ps_cont.comp (by fun_prop)
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub (f := fun a : ℝ => a + x + U / 2)
      (g := fun a => (ps (a + (x + U - Q)) - ps (a + (x - Q))) / U)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (((hc1.sub hc2).div_const U).intervalIntegrable _ _)]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (f := fun a => ps (a + (x + U - Q)))
    (g := fun a => ps (a + (x - Q))) (hc1.intervalIntegrable _ _)
    (hc2.intervalIntegrable _ _), int_ps_shift _ _ _ (by linarith),
    int_ps_shift _ _ _ (by linarith)]
  rw [intervalIntegral.integral_add (f := fun a : ℝ => a + x) (Continuous.intervalIntegrable (by fun_prop) _ _)
    intervalIntegrable_const, intervalIntegral.integral_add (f := fun a : ℝ => a)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    intervalIntegrable_const, integral_id]
  simp
  have e1 : x + U + (x + U - Q) = 2 * x + 2 * U - Q := by ring
  have e2 : x + (x + U - Q) = 2 * x + U - Q := by ring
  have e3 : x + U + (x - Q) = 2 * x + U - Q := by ring
  have e4 : x + (x - Q) = 2 * x - Q := by ring
  rw [e1, e2, e3, e4]
  field_simp
  ring


lemma reg0 (p x U cF Q : ℝ) (hx : 0 ≤ x) (hU : 0 < U) (hQ : Q ≤ 2 * x) :
    piF p x U cF Q = (p - cF) * Q := by
  rw [piF_formula p x U cF Q hx hU]; unfold Ps
  rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]
  field_simp; ring

lemma reg1 (p x U cF Q : ℝ) (hx : 0 ≤ x) (hU : 0 < U) (hQ : 2 * x ≤ Q) (hQ' : Q ≤ 2 * x + U) :
    piF p x U cF Q = p * (Q - (Q - 2 * x) ^ 3 / (6 * U ^ 2)) - cF * Q := by
  rw [piF_formula p x U cF Q hx hU]; unfold Ps
  rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_right (by linarith)]
  field_simp; ring

lemma reg2 (p x U cF Q : ℝ) (hx : 0 ≤ x) (hU : 0 < U) (hQ : 2 * x + U ≤ Q)
    (hQ' : Q ≤ 2 * x + 2 * U) :
    piF p x U cF Q = p * (2 * x + U - (2 * x + 2 * U - Q) ^ 3 / (6 * U ^ 2)) - cF * Q := by
  rw [piF_formula p x U cF Q hx hU]; unfold Ps
  rw [max_eq_left (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
  field_simp; ring

lemma reg3 (p x U cF Q : ℝ) (hx : 0 ≤ x) (hU : 0 < U) (hQ : 2 * x + 2 * U ≤ Q) :
    piF p x U cF Q = p * (2 * x + U) - cF * Q := by
  rw [piF_formula p x U cF Q hx hU]; unfold Ps
  rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
  field_simp; ring

lemma caseA (p x U cF w : ℝ) (hx : 0 ≤ x) (hU : 0 < U) (hp : 0 < p) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hcF : cF = p * w ^ 2 / 2) :
    piF p x U cF (2 * x + (2 - w) * U) = 2 * (p - cF) * x + 2 / 3 * cF * (w - 3) * U + p * U ∧
    ∀ Q, piF p x U cF Q ≤ 2 * (p - cF) * x + 2 / 3 * cF * (w - 3) * U + p * U := by
  subst hcF
  have hU2 : 0 < U ^ 2 := by positivity
  constructor
  · rw [reg2 p x U _ _ hx hU (by nlinarith) (by nlinarith)]
    field_simp; ring
  intro Q
  rcases le_total Q (2 * x) with h0 | h0
  · rw [reg0 p x U _ Q hx hU h0]
    have : 2 * (p - p * w ^ 2 / 2) * x + 2 / 3 * (p * w ^ 2 / 2) * (w - 3) * U + p * U -
        (p - p * w ^ 2 / 2) * Q =
        (p - p * w ^ 2 / 2) * (2 * x - Q) + p * U * (1 - w ^ 2) + p * w ^ 3 * U / 3 := by ring
    have hw2 : w ^ 2 ≤ 1 := by nlinarith
    have h1 : 0 ≤ (p - p * w ^ 2 / 2) * (2 * x - Q) :=
      mul_nonneg (by nlinarith [mul_le_mul_of_nonneg_left hw2 hp.le]) (by linarith)
    have h2 : 0 ≤ p * U * (1 - w ^ 2) := mul_nonneg (by positivity) (by nlinarith)
    have h3 : 0 ≤ p * w ^ 3 * U / 3 := by positivity
    linarith
  rcases le_total Q (2 * x + U) with h1 | h1
  · rw [reg1 p x U _ Q hx hU h0 h1]
    set s := Q - 2 * x with hs
    have hQ : Q = 2 * x + s := by rw [hs]; ring
    rw [hQ]
    have key : 2 * (p - p * w ^ 2 / 2) * x + 2 / 3 * (p * w ^ 2 / 2) * (w - 3) * U + p * U -
        (p * (2 * x + s - s ^ 3 / (6 * U ^ 2)) - p * w ^ 2 / 2 * (2 * x + s)) =
        p / (6 * U ^ 2) * ((U - w * U) ^ 2 * (U + 2 * w * U)) +
        (U - s) * (p * (6 * U ^ 2 - 3 * w ^ 2 * U ^ 2 - (U ^ 2 + U * s + s ^ 2))) / (6 * U ^ 2) := by
      field_simp; ring
    have hA : 0 ≤ p / (6 * U ^ 2) * ((U - w * U) ^ 2 * (U + 2 * w * U)) := by
      apply mul_nonneg (by positivity)
      apply mul_nonneg (sq_nonneg _); nlinarith
    have hs0 : 0 ≤ s := by linarith
    have hs1 : s ≤ U := by linarith
    have hB : 0 ≤ (U - s) * (p * (6 * U ^ 2 - 3 * w ^ 2 * U ^ 2 - (U ^ 2 + U * s + s ^ 2))) /
        (6 * U ^ 2) := by
      apply div_nonneg _ (by positivity)
      apply mul_nonneg (by linarith)
      apply mul_nonneg hp.le
      have : w ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul hs1 hs1 hs0 hU.le, mul_le_mul_of_nonneg_left hs1 hU.le,
        mul_le_mul_of_nonneg_right this (le_of_lt hU2)]
    linarith
  rcases le_total Q (2 * x + 2 * U) with h2 | h2
  · rw [reg2 p x U _ Q hx hU h1 h2]
    set u := 2 * x + 2 * U - Q with hu
    have hQ : Q = 2 * x + 2 * U - u := by rw [hu]; ring
    rw [hQ]
    have key : 2 * (p - p * w ^ 2 / 2) * x + 2 / 3 * (p * w ^ 2 / 2) * (w - 3) * U + p * U -
        (p * (2 * x + U - u ^ 3 / (6 * U ^ 2)) - p * w ^ 2 / 2 * (2 * x + 2 * U - u)) =
        p / (6 * U ^ 2) * ((u - w * U) ^ 2 * (u + 2 * w * U)) := by
      field_simp; ring
    have hu0 : 0 ≤ u := by linarith
    have hA : 0 ≤ p / (6 * U ^ 2) * ((u - w * U) ^ 2 * (u + 2 * w * U)) := by
      apply mul_nonneg (by positivity)
      apply mul_nonneg (sq_nonneg _); nlinarith
    linarith
  · rw [reg3 p x U _ Q hx hU h2]
    have key : 2 * (p - p * w ^ 2 / 2) * x + 2 / 3 * (p * w ^ 2 / 2) * (w - 3) * U + p * U -
        (p * (2 * x + U) - p * w ^ 2 / 2 * Q) =
        p * w ^ 3 * U / 3 + p * w ^ 2 / 2 * (Q - 2 * x - 2 * U) := by ring
    have : 0 ≤ p * w ^ 3 * U / 3 := by positivity
    have : 0 ≤ p * w ^ 2 / 2 * (Q - 2 * x - 2 * U) := mul_nonneg (by positivity) (by linarith)
    linarith

lemma caseB (p x U cF z : ℝ) (hx : 0 ≤ x) (hU : 0 < U) (hp : 0 < p) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hcF : cF = p - p * z ^ 2 / 2) :
    piF p x U cF (2 * x + z * U) = 2 * (p - cF) * x + 2 / 3 * (p - cF) * z * U ∧
    ∀ Q, piF p x U cF Q ≤ 2 * (p - cF) * x + 2 / 3 * (p - cF) * z * U := by
  subst hcF
  have hU2 : 0 < U ^ 2 := by positivity
  constructor
  · rw [reg1 p x U _ _ hx hU (by nlinarith) (by nlinarith)]
    field_simp; ring
  intro Q
  rcases le_total Q (2 * x) with h0 | h0
  · rw [reg0 p x U _ Q hx hU h0]
    have : 0 ≤ p * z ^ 2 / 2 * (2 * x - Q) := mul_nonneg (by positivity) (by linarith)
    have : 0 ≤ p * z ^ 2 / 2 * z * U := by positivity
    nlinarith
  rcases le_total Q (2 * x + U) with h1 | h1
  · rw [reg1 p x U _ Q hx hU h0 h1]
    set s := Q - 2 * x with hs
    have hQ : Q = 2 * x + s := by rw [hs]; ring
    rw [hQ]
    have key : 2 * (p - (p - p * z ^ 2 / 2)) * x + 2 / 3 * (p - (p - p * z ^ 2 / 2)) * z * U -
        (p * (2 * x + s - s ^ 3 / (6 * U ^ 2)) - (p - p * z ^ 2 / 2) * (2 * x + s)) =
        p / (6 * U ^ 2) * ((s - z * U) ^ 2 * (s + 2 * z * U)) := by
      field_simp; ring
    have hs0 : 0 ≤ s := by linarith
    have hA : 0 ≤ p / (6 * U ^ 2) * ((s - z * U) ^ 2 * (s + 2 * z * U)) := by
      apply mul_nonneg (by positivity)
      apply mul_nonneg (sq_nonneg _); nlinarith
    linarith
  have hz2 : z ^ 2 ≤ 1 := by nlinarith
  have hA : 0 ≤ p / (6 * U ^ 2) * ((U - z * U) ^ 2 * (U + 2 * z * U)) := by
    apply mul_nonneg (by positivity)
    apply mul_nonneg (sq_nonneg _); nlinarith
  rcases le_total Q (2 * x + 2 * U) with h2 | h2
  · rw [reg2 p x U _ Q hx hU h1 h2]
    set u := 2 * x + 2 * U - Q with hu
    have hQ : Q = 2 * x + 2 * U - u := by rw [hu]; ring
    rw [hQ]
    have key : 2 * (p - (p - p * z ^ 2 / 2)) * x + 2 / 3 * (p - (p - p * z ^ 2 / 2)) * z * U -
        (p * (2 * x + U - u ^ 3 / (6 * U ^ 2)) - (p - p * z ^ 2 / 2) * (2 * x + 2 * U - u)) =
        p / (6 * U ^ 2) * ((U - z * U) ^ 2 * (U + 2 * z * U)) +
        (U - u) * (6 * U ^ 2 * (p - p * z ^ 2 / 2) - p * (U ^ 2 + U * u + u ^ 2)) / (6 * U ^ 2) := by
      field_simp; ring
    have hu0 : 0 ≤ u := by linarith
    have hu1 : u ≤ U := by linarith
    have hB : 0 ≤ (U - u) * (6 * U ^ 2 * (p - p * z ^ 2 / 2) - p * (U ^ 2 + U * u + u ^ 2)) /
        (6 * U ^ 2) := by
      apply div_nonneg _ (by positivity)
      apply mul_nonneg (by linarith)
      have e : 6 * U ^ 2 * (p - p * z ^ 2 / 2) - p * (U ^ 2 + U * u + u ^ 2) =
          p * (6 * U ^ 2 - 3 * z ^ 2 * U ^ 2 - (U ^ 2 + U * u + u ^ 2)) := by ring
      rw [e]
      apply mul_nonneg hp.le
      nlinarith [mul_le_mul hu1 hu1 hu0 hU.le, mul_le_mul_of_nonneg_left hu1 hU.le,
        mul_le_mul_of_nonneg_right hz2 (le_of_lt hU2)]
    linarith
  · rw [reg3 p x U _ Q hx hU h2]
    have key : 2 * (p - (p - p * z ^ 2 / 2)) * x + 2 / 3 * (p - (p - p * z ^ 2 / 2)) * z * U -
        (p * (2 * x + U) - (p - p * z ^ 2 / 2) * Q) =
        p / (6 * U ^ 2) * ((U - z * U) ^ 2 * (U + 2 * z * U)) +
        U * (6 * U ^ 2 * (p - p * z ^ 2 / 2) - p * U ^ 2) / (6 * U ^ 2) +
        (p - p * z ^ 2 / 2) * (Q - 2 * x - 2 * U) := by
      field_simp; ring
    have hB : 0 ≤ U * (6 * U ^ 2 * (p - p * z ^ 2 / 2) - p * U ^ 2) / (6 * U ^ 2) := by
      apply div_nonneg _ (by positivity)
      apply mul_nonneg hU.le
      nlinarith [mul_le_mul_of_nonneg_right hz2 (le_of_lt hU2)]
    have hC : 0 ≤ (p - p * z ^ 2 / 2) * (Q - 2 * x - 2 * U) :=
      mul_nonneg (by nlinarith) (by linarith)
    linarith


noncomputable def g1 (p x U cF : ℝ) : ℝ :=
  2 * (p - cF) * x + 2 / 3 * cF * (Real.sqrt (2 * cF / p) - 3) * U + p * U
noncomputable def g2 (p x U cF : ℝ) : ℝ :=
  2 * (p - cF) * x + 2 / 3 * (p - cF) * Real.sqrt (2 - 2 * cF / p) * U

lemma bdd (p x U cF : ℝ) (hx : 0 ≤ x) (hU : 0 < U) (hp : 0 < p) (hcF0 : 0 ≤ cF) (hcFp : cF ≤ p) :
    ∃ Q, 0 ≤ Q ∧ (cF < p → 0 < Q) ∧ piF p x U cF Q = piBarF p x U cF ∧
      BddAbove (piF p x U cF '' Set.Ici 0) ∧
      (2 * cF ≤ p → piBarF p x U cF = g1 p x U cF) ∧
      (p ≤ 2 * cF → piBarF p x U cF = g2 p x U cF) := by
  rcases le_or_gt (2 * cF) p with h2 | h2
  · set w := Real.sqrt (2 * cF / p) with hw
    have hw0 : 0 ≤ w := Real.sqrt_nonneg _
    have hr : 2 * cF / p ≤ 1 := by rw [div_le_one hp]; linarith
    have hw1 : w ≤ 1 := Real.sqrt_le_one.mpr hr
    have hw2 : w ^ 2 = 2 * cF / p := Real.sq_sqrt (by positivity)
    have hcF' : cF = p * w ^ 2 / 2 := by rw [hw2]; field_simp
    obtain ⟨hv, hb⟩ := caseA p x U cF w hx hU hp hw0 hw1 hcF'
    have hG : IsGreatest (piF p x U cF '' Set.Ici 0)
        (2 * (p - cF) * x + 2 / 3 * cF * (w - 3) * U + p * U) := by
      refine ⟨⟨_, ?_, hv⟩, ?_⟩
      · show 0 ≤ 2 * x + (2 - w) * U
        nlinarith
      · rintro _ ⟨Q, _, rfl⟩; exact hb Q
    have hs := hG.csSup_eq
    refine ⟨2 * x + (2 - w) * U, by nlinarith, fun _ => by nlinarith, ?_, hG.bddAbove, ?_, ?_⟩
    · rw [hv]; exact hs.symm
    · intro _; exact hs
    · intro h3
      have hc : cF = p / 2 := by linarith
      have : piBarF p x U cF = g1 p x U cF := hs
      rw [this]; unfold g1 g2
      rw [hc]
      have e1 : 2 * (p / 2) / p = 1 := by field_simp
      have e2 : 2 - 2 * (p / 2) / p = 1 := by field_simp; ring
      rw [e1, show (2:ℝ) - 1 = 1 by norm_num, Real.sqrt_one]; ring
  · set z := Real.sqrt (2 - 2 * cF / p) with hz
    have hz0 : 0 ≤ z := Real.sqrt_nonneg _
    have hr0 : 0 ≤ 2 - 2 * cF / p := by
      have : cF / p ≤ 1 := by rw [div_le_one hp]; linarith
      have : 2 * cF / p = 2 * (cF / p) := by ring
      linarith
    have hr : 2 - 2 * cF / p ≤ 1 := by
      have : 1 ≤ 2 * cF / p := by rw [le_div_iff₀ hp]; linarith
      linarith
    have hz1 : z ≤ 1 := Real.sqrt_le_one.mpr hr
    have hz2 : z ^ 2 = 2 - 2 * cF / p := Real.sq_sqrt hr0
    have hcF' : cF = p - p * z ^ 2 / 2 := by rw [hz2]; field_simp; ring
    obtain ⟨hv, hb⟩ := caseB p x U cF z hx hU hp hz0 hz1 hcF'
    have hG : IsGreatest (piF p x U cF '' Set.Ici 0)
        (2 * (p - cF) * x + 2 / 3 * (p - cF) * z * U) := by
      refine ⟨⟨_, ?_, hv⟩, ?_⟩
      · show 0 ≤ 2 * x + z * U
        positivity
      · rintro _ ⟨Q, _, rfl⟩; exact hb Q
    have hs := hG.csSup_eq
    refine ⟨2 * x + z * U, by positivity, ?_, ?_, hG.bddAbove, fun h => absurd h (by linarith),
      fun _ => hs⟩
    · intro hlt
      have : 0 < z := by
        rw [hz]; apply Real.sqrt_pos.mpr
        have : cF / p < 1 := by rw [div_lt_one hp]; linarith
        have : 2 * cF / p = 2 * (cF / p) := by ring
        linarith
      positivity
    · rw [hv]; exact hs.symm

lemma piF_sub (p x U a b Q : ℝ) : piF p x U a Q = piF p x U b Q + (b - a) * Q := by
  unfold piF; ring

lemma g_pos (p x U a : ℝ) (hx : 0 ≤ x) (hU : 0 < U) (hp : 0 < p) (ha0 : 0 ≤ a) (hap : a < p) :
    0 < piBarF p x U a := by
  obtain ⟨_, _, _, _, _, h1, h2⟩ := bdd p x U a hx hU hp ha0 hap.le
  rcases le_or_gt (2 * a) p with h | h
  · rw [h1 h]; unfold g1
    set w := Real.sqrt (2 * a / p) with hw
    have hw0 : 0 ≤ w := Real.sqrt_nonneg _
    have hr : 2 * a / p ≤ 1 := by rw [div_le_one hp]; linarith
    have hw1 : w ≤ 1 := Real.sqrt_le_one.mpr hr
    have hw2 : w ^ 2 = 2 * a / p := Real.sq_sqrt (by positivity)
    have ha' : a = p * w ^ 2 / 2 := by rw [hw2]; field_simp
    rw [ha']
    have e : 2 / 3 * (p * w ^ 2 / 2) * (w - 3) * U + p * U =
        p * U * ((1 - w ^ 2) + w ^ 3 / 3) := by ring
    have h3 : 0 ≤ 2 * (p - p * w ^ 2 / 2) * x := by
      apply mul_nonneg _ hx; nlinarith
    have h4 : 0 < (1 - w ^ 2) + w ^ 3 / 3 := by
      rcases eq_or_lt_of_le hw0 with h0 | h0
      · rw [← h0]; norm_num
      · have : 0 < w ^ 3 := by positivity
        nlinarith
    have : 0 < p * U * ((1 - w ^ 2) + w ^ 3 / 3) := by positivity
    linarith
  · rw [h2 h.le]; unfold g2
    have : 0 < Real.sqrt (2 - 2 * a / p) := by
      apply Real.sqrt_pos.mpr
      have : a / p < 1 := by rw [div_lt_one hp]; linarith
      have : 2 * a / p = 2 * (a / p) := by ring
      linarith
    have : 0 ≤ 2 * (p - a) * x := by apply mul_nonneg _ hx; linarith
    have : 0 < 2 / 3 * (p - a) * Real.sqrt (2 - 2 * a / p) * U := by
      have : 0 < p - a := by linarith
      positivity
    linarith

lemma g_at_p (p x U : ℝ) (hx : 0 ≤ x) (hU : 0 < U) (hp : 0 < p) : piBarF p x U p = 0 := by
  obtain ⟨_, _, _, _, _, _, h2⟩ := bdd p x U p hx hU hp hp.le le_rfl
  rw [h2 (by linarith)]; unfold g2; ring

lemma strictAnti (p x U : ℝ) (hx : 0 ≤ x) (hU : 0 < U) (hp : 0 < p) (a b : ℝ) (ha : 0 ≤ a)
    (hab : a < b) (hb : b ≤ p) : piBarF p x U b < piBarF p x U a := by
  rcases eq_or_lt_of_le hb with hbp | hbp
  · rw [hbp, g_at_p p x U hx hU hp]; exact g_pos p x U a hx hU hp ha (by linarith)
  · obtain ⟨Q, hQ0, hQpos, hQv, _, _, _⟩ := bdd p x U b hx hU hp (by linarith) hb
    obtain ⟨_, _, _, _, hbddA, _, _⟩ := bdd p x U a hx hU hp ha (by linarith)
    have hQ := hQpos hbp
    have h1 : piF p x U a Q ≤ piBarF p x U a := le_csSup hbddA ⟨Q, hQ0, rfl⟩
    rw [piF_sub p x U a b Q] at h1
    rw [← hQv]
    nlinarith

end FlexLAuxB

open FlexLAuxB

theorem solution (p c x U : ℝ) (hc : 0 ≤ c) (hcp : c < p) (hx : 0 ≤ x) (hU : 0 < U) :
    StrictAntiOn (fun cF : ℝ => piBarF p x U cF - piBarN p c x U) (Set.Icc 0 p) ∧
    ∃! cF : ℝ, cF ∈ Set.Ico c p ∧ IsBreakEven p c x U cF := by
  have hp : 0 < p := by linarith
  have hN := FlexLearning.Threshold.piBarN_eq p c x U hc hcp hx hU
  have hSA : StrictAntiOn (fun cF : ℝ => piBarF p x U cF - piBarN p c x U) (Set.Icc 0 p) := by
    intro a ha b hb hab
    simp only
    linarith [strictAnti p x U hx hU hp a b ha.1 hab hb.2]
  refine ⟨hSA, ?_⟩
  -- the break-even value N and the comparison at cF = c
  set N := piBarN p c x U with hNdef
  have hNpos : 0 < N := by
    rw [hN]
    have : 0 < U * ((p - c) ^ 2 / p) := by
      have : 0 < p - c := by linarith
      positivity
    have : 0 ≤ 2 * (p - c) * x := by apply mul_nonneg _ hx; linarith
    linarith
  -- g1 and g2 relative to N
  have hc_ge : N ≤ piBarF p x U c := by
    obtain ⟨_, _, _, _, _, h1, h2⟩ := bdd p x U c hx hU hp hc hcp.le
    rw [hN]
    rcases le_or_gt (2 * c) p with h | h
    · rw [h1 h]; unfold g1
      set w := Real.sqrt (2 * c / p) with hw
      have hw0 : 0 ≤ w := Real.sqrt_nonneg _
      have hr : 2 * c / p ≤ 1 := by rw [div_le_one hp]; linarith
      have hw1 : w ≤ 1 := Real.sqrt_le_one.mpr hr
      have hw2 : w ^ 2 = 2 * c / p := Real.sq_sqrt (by positivity)
      have hc' : c = p * w ^ 2 / 2 := by rw [hw2]; field_simp
      rw [hc']
      have e : 2 * (p - p * w ^ 2 / 2) * x + 2 / 3 * (p * w ^ 2 / 2) * (w - 3) * U + p * U -
          (2 * (p - p * w ^ 2 / 2) * x + U * ((p - p * w ^ 2 / 2) ^ 2 / p)) =
          p * U * (w ^ 3 * (4 - 3 * w)) / 12 := by field_simp; ring
      have : 0 ≤ p * U * (w ^ 3 * (4 - 3 * w)) / 12 := by
        apply div_nonneg _ (by norm_num)
        apply mul_nonneg (by positivity)
        apply mul_nonneg (by positivity); linarith
      linarith
    · rw [h2 h.le]; unfold g2
      set z := Real.sqrt (2 - 2 * c / p) with hz
      have hz0 : 0 ≤ z := Real.sqrt_nonneg _
      have hr0 : 0 ≤ 2 - 2 * c / p := by
        have : c / p ≤ 1 := by rw [div_le_one hp]; linarith
        have : 2 * c / p = 2 * (c / p) := by ring
        linarith
      have hr : 2 - 2 * c / p ≤ 1 := by
        have : 1 ≤ 2 * c / p := by rw [le_div_iff₀ hp]; linarith
        linarith
      have hz1 : z ≤ 1 := Real.sqrt_le_one.mpr hr
      have hz2 : z ^ 2 = 2 - 2 * c / p := Real.sq_sqrt hr0
      have hc' : c = p - p * z ^ 2 / 2 := by rw [hz2]; field_simp; ring
      rw [hc']
      have e : 2 * (p - (p - p * z ^ 2 / 2)) * x + 2 / 3 * (p - (p - p * z ^ 2 / 2)) * z * U -
          (2 * (p - (p - p * z ^ 2 / 2)) * x + U * ((p - (p - p * z ^ 2 / 2)) ^ 2 / p)) =
          p * U * (z ^ 3 * (4 - 3 * z)) / 12 := by field_simp; ring
      have : 0 ≤ p * U * (z ^ 3 * (4 - 3 * z)) / 12 := by
        apply div_nonneg _ (by norm_num)
        apply mul_nonneg (by positivity)
        apply mul_nonneg (by positivity); linarith
      linarith
  -- continuity of the two closed-form branches
  have hcont1 : Continuous (g1 p x U) := by unfold g1; fun_prop
  have hcont2 : Continuous (g2 p x U) := by unfold g2; fun_prop
  have hp0 : piBarF p x U p = 0 := g_at_p p x U hx hU hp
  -- existence of a root in [c, p]
  have hex : ∃ cF ∈ Set.Icc c p, piBarF p x U cF = N := by
    rcases le_or_gt (2 * c) p with hcl | hcl
    · -- c ≤ p/2
      by_cases hmid : piBarF p x U (p / 2) ≤ N
      · have hmem : N ∈ Set.Icc (g1 p x U (p / 2)) (g1 p x U c) := by
          obtain ⟨_, _, _, _, _, h1, _⟩ := bdd p x U (p / 2) hx hU hp (by linarith) (by linarith)
          obtain ⟨_, _, _, _, _, h1', _⟩ := bdd p x U c hx hU hp hc hcp.le
          rw [← h1 (by linarith), ← h1' hcl]
          exact ⟨hmid, hc_ge⟩
        obtain ⟨cF, hcF, hval⟩ := intermediate_value_Icc' (show c ≤ p / 2 by linarith)
          hcont1.continuousOn hmem
        refine ⟨cF, ⟨hcF.1, by linarith [hcF.2]⟩, ?_⟩
        obtain ⟨_, _, _, _, _, h1, _⟩ :=
          bdd p x U cF hx hU hp (by linarith [hcF.1]) (by linarith [hcF.2])
        rw [h1 (by linarith [hcF.2]), hval]
      · push Not at hmid
        have hmem : N ∈ Set.Icc (g2 p x U p) (g2 p x U (p / 2)) := by
          obtain ⟨_, _, _, _, _, _, h2⟩ := bdd p x U (p / 2) hx hU hp (by linarith) (by linarith)
          obtain ⟨_, _, _, _, _, _, h2'⟩ := bdd p x U p hx hU hp hp.le le_rfl
          rw [← h2 (by linarith), ← h2' (by linarith), hp0]
          exact ⟨hNpos.le, hmid.le⟩
        obtain ⟨cF, hcF, hval⟩ := intermediate_value_Icc' (show p / 2 ≤ p by linarith)
          hcont2.continuousOn hmem
        refine ⟨cF, ⟨by linarith [hcF.1], hcF.2⟩, ?_⟩
        obtain ⟨_, _, _, _, _, _, h2⟩ := bdd p x U cF hx hU hp (by linarith [hcF.1]) hcF.2
        rw [h2 (by linarith [hcF.1]), hval]
    · have hmem : N ∈ Set.Icc (g2 p x U p) (g2 p x U c) := by
        obtain ⟨_, _, _, _, _, _, h2⟩ := bdd p x U c hx hU hp hc hcp.le
        obtain ⟨_, _, _, _, _, _, h2'⟩ := bdd p x U p hx hU hp hp.le le_rfl
        rw [← h2 hcl.le, ← h2' (by linarith), hp0]
        exact ⟨hNpos.le, hc_ge⟩
      obtain ⟨cF, hcF, hval⟩ := intermediate_value_Icc' hcp.le hcont2.continuousOn hmem
      refine ⟨cF, hcF, ?_⟩
      obtain ⟨_, _, _, _, _, _, h2⟩ := bdd p x U cF hx hU hp (by linarith [hcF.1]) hcF.2
      rw [h2 (by linarith [hcF.1]), hval]
  obtain ⟨cF, hcF, hval⟩ := hex
  have hcFp : cF < p := by
    rcases eq_or_lt_of_le hcF.2 with h | h
    · rw [h, hp0] at hval; linarith
    · exact h
  refine ⟨cF, ⟨⟨hcF.1, hcFp⟩, hval⟩, ?_⟩
  rintro y ⟨hy, hyv⟩
  unfold IsBreakEven at hyv
  apply hSA.injOn ⟨by linarith [hy.1], hy.2.le⟩ ⟨by linarith [hcF.1], hcF.2⟩
  simp only
  rw [hyv, hval]
