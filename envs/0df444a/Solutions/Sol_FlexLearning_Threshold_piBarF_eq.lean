-- Prove2me | solution 1 for FlexLearning.Threshold.piBarF_eq
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T10:42:01.743655+00:00
-- url     : https://prove2.me/submissions/9ab20c75-c562-4d1b-b9df-3240f9c60ecc

import Mathlib
import Definitions.Def_FlexLearning_Threshold_Model

open FlexLearning.Threshold MeasureTheory

namespace FlexLAuxF

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

end FlexLAuxF

open FlexLAuxF

theorem solution (p x U cF : ℝ) (hcF : 0 ≤ cF) (hcFp : cF < p) (hx : 0 ≤ x) (hU : 0 < U) :
    (2 * cF ≤ p →
      piF p x U cF (2 * x + (2 - Real.sqrt (2 * cF / p)) * U) = piBarF p x U cF ∧
      piBarF p x U cF =
        2 * (p - cF) * x + 2 / 3 * cF * (Real.sqrt (2 * cF / p) - 3) * U + p * U) ∧
    (p < 2 * cF →
      piF p x U cF (2 * x + Real.sqrt (2 - 2 * cF / p) * U) = piBarF p x U cF ∧
      piBarF p x U cF = 2 * (p - cF) * x + 2 / 3 * (p - cF) * Real.sqrt (2 - 2 * cF / p) * U) := by
  have hp : 0 < p := by linarith
  constructor
  · intro h2
    set w := Real.sqrt (2 * cF / p) with hw
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
    have hs : piBarF p x U cF = 2 * (p - cF) * x + 2 / 3 * cF * (w - 3) * U + p * U :=
      hG.csSup_eq
    exact ⟨hv.trans hs.symm, hs⟩
  · intro h2
    set z := Real.sqrt (2 - 2 * cF / p) with hz
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
    have hs : piBarF p x U cF = 2 * (p - cF) * x + 2 / 3 * (p - cF) * z * U := hG.csSup_eq
    exact ⟨hv.trans hs.symm, hs⟩
