-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.normalized_finite_brownian_sum
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:04:36.814878+00:00
-- url     : https://prove2.me/submissions/2494ed70-439b-404c-bb3c-17b413fd2815

import Theorems.Thm_ManyServerQED_Scheduling_independent_brownian_normalized_linear_combination

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

set_option maxHeartbeats 1450000 in
theorem solution {Ω I : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (B : I → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsBrownianReal (B i) P)
    (hM : ∀ i, AEMeasurable (fun ω t => B i t ω) P)
    (hI : iIndepFun (fun i ω t => B i t ω) P)
    (c : I → ℝ) (s : Finset I) (hs : 0 < ∑ i ∈ s, c i^2) :
    IsBrownianReal (fun t ω => (∑ i ∈ s, c i*B i t ω) / Real.sqrt (∑ i ∈ s, c i^2)) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert i s hi ih =>
    let V := ∑ j ∈ s, c j^2
    let W := Real.sqrt (c i^2+V)
    have hv : 0 ≤ V := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hW : 0 < W := Real.sqrt_pos.2 (by simpa only [Finset.sum_insert hi] using hs)
    simp only [Finset.sum_insert hi]
    change IsBrownianReal (fun t ω => (c i*B i t ω+∑ j ∈ s, c j*B j t ω)/W) P
    rcases hv.eq_or_lt with hv | hv
    · have hc (j : I) (hj : j ∈ s) : c j = 0 := by
        have h := Finset.single_le_sum (f := fun j => c j^2)
          (fun j _ => sq_nonneg (c j)) hj
        change c j^2 ≤ V at h
        nlinarith only [h,hv]
      have hZ (t : ℝ≥0) (ω : Ω) : ∑ j ∈ s, c j*B j t ω = 0 :=
        Finset.sum_eq_zero fun j hj => by rw [hc j hj,zero_mul]
      have hAbs : W = |c i| := by simp only [W,←hv,add_zero,Real.sqrt_sq_eq_abs]
      by_cases h : 0 ≤ c i
      · have hEq : (fun t ω => (c i*B i t ω+∑ j ∈ s, c j*B j t ω)/W) = B i := by
          funext t ω
          rw [hZ,add_zero,hAbs,abs_of_nonneg h]
          have hNe : c i ≠ 0 := by simpa [hAbs,abs_of_nonneg h] using hW.ne'
          field_simp
        rw [hEq]
        exact hB i
      · have hEq : (fun t ω => (c i*B i t ω+∑ j ∈ s, c j*B j t ω)/W) =
            (fun t ω => -B i t ω) := by
          funext t ω
          rw [hZ,add_zero,hAbs,abs_of_neg (lt_of_not_ge h)]
          have hNe := (lt_of_not_ge h).ne
          field_simp
        rw [hEq]
        exact (hB i).neg
    · let C (t : ℝ≥0) (ω : Ω) := (∑ j ∈ s, c j*B j t ω) / Real.sqrt V
      have hC : IsBrownianReal C P := ih hv
      let a (j : I) := if j = i then 1 else c j / Real.sqrt V
      let F (j : I) (ω : Ω) (t : ℝ≥0) := a j * B j t ω
      have hfm (j : I) : Measurable (fun (g : ℝ≥0 → ℝ) t => a j*g t) :=
        measurable_pi_lambda _ (fun t => (show Measurable (fun g : ℝ≥0 → ℝ => g t) from measurable_pi_apply t).const_mul (a j))
      have hF : iIndepFun F P := hI.comp (fun j (g : ℝ≥0 → ℝ) t => a j*g t) hfm
      have hFM (j : I) : AEMeasurable (F j) P := (hfm j).comp_aemeasurable (hM j)
      have hHead : F i = (fun ω t => B i t ω) := by funext ω t; simp [F,a]
      have hTail : (∑ j ∈ s,F j) = (fun ω t => C t ω) := by
        funext ω t
        simp only [Finset.sum_apply,F,C]
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j hj
        have hne : j ≠ i := fun h => hi (h ▸ hj)
        simp only [a,if_neg hne]
        ring
      have hInd := (hF.indepFun_finsetSum_of_notMem₀ hFM hi).symm
      rw [hHead,hTail] at hInd
      have hv' : 0 < Real.sqrt V := Real.sqrt_pos.2 hv
      have hWF : W^2 = c i^2+V := Real.sq_sqrt (by positivity)
      have hWNorm : (c i/W)^2+(Real.sqrt V/W)^2=1 := by
        simp only [div_pow,Real.sq_sqrt hv.le,←add_div,hWF]
        exact div_self (by positivity)
      have hlaw := ManyServerQED.Scheduling.independent_brownian_normalized_linear_combination
        (B i) C (hB i) hC hInd (c i/W) (Real.sqrt V/W) hWNorm
      have hEq : (fun t ω => c i/W*B i t ω + Real.sqrt V/W*C t ω) =
          (fun t ω => (c i*B i t ω+∑ j ∈ s, c j*B j t ω)/W) := by
        funext t ω
        dsimp only [C]
        field_simp [hW.ne',hv'.ne']
      exact hEq ▸ hlaw
