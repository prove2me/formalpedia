-- Prove2me | solution 1 for BenfordLaw.exponential_growth_benford
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:53:56.907745+00:00
-- url     : https://prove2.me/submissions/3bb8217e-6dfc-4b87-86db-71a0d0caa3e4

import Mathlib
import Definitions.Def_BenfordLaw_Defs
open BenfordLaw MeasureTheory

lemma fract_indicator_integral (α β : ℝ) (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 1) :
    ∫ u in (0 : ℝ)..1, (Set.Ico α β).indicator (1 : ℝ → ℝ) (Int.fract u) = β - α := by
  have hae : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Set.uIoc (0 : ℝ) 1 →
      (Set.Ico α β).indicator (1 : ℝ → ℝ) (Int.fract u) = (Set.Ico α β).indicator 1 u := by
    have : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 1 := by
      rw [ae_iff]; simp
    filter_upwards [this] with u hu1 hu
    rw [Set.uIoc_of_le zero_le_one, Set.mem_Ioc] at hu
    rw [Int.fract_eq_self.mpr ⟨hu.1.le, lt_of_le_of_ne hu.2 hu1⟩]
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_of_le zero_le_one,
    integral_indicator measurableSet_Ico, Measure.restrict_restrict measurableSet_Ico]
  simp only [Pi.one_apply, integral_const, smul_eq_mul, mul_one]
  have h1 : (Set.Ico α β ∩ Set.Ioc 0 1 : Set ℝ) =ᵐ[(volume : Measure ℝ)] (Set.Ico α β : Set ℝ) := by
    have hsub : Set.Ioo α β ⊆ Set.Ico α β ∩ Set.Ioc 0 1 := fun x hx =>
      ⟨Set.Ioo_subset_Ico_self hx, by constructor <;> linarith [hx.1, hx.2]⟩
    refine (ae_eq_of_subset_of_measure_ge Set.inter_subset_left ?_ ?_ ?_)
    · rw [Real.volume_Ico, ← Real.volume_Ioo]; exact measure_mono hsub
    · exact (measurableSet_Ico.inter measurableSet_Ioc).nullMeasurableSet
    · show volume (Set.Ico α β) ≠ ⊤
      rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top
  rw [Measure.real, Measure.restrict_apply_univ, measure_congr h1, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]


lemma leadingDigit_eq_iff_aux' (x : ℝ) (d : ℕ) (hd1 : 1 ≤ d) :
    leadingDigit 10 x = d ↔
      Int.fract (Real.logb 10 x) ∈ Set.Ico (Real.logb 10 d) (Real.logb 10 (d + 1)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  unfold leadingDigit
  rw [Nat.floor_eq_iff (by positivity), Set.mem_Ico]
  push_cast
  rw [Real.logb_le_iff_le_rpow (by norm_num) hd0,
    Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity)]

theorem solution (C r : ℝ) (hC : 0 < C) (hr : r ≠ 0)
    (d : ℕ) (hd1 : 1 ≤ d) (hd9 : d ≤ 9) :
    Filter.Tendsto
      (fun T : ℝ =>
        (MeasureTheory.volume
          {t : ℝ | t ∈ Set.Icc 0 T ∧ leadingDigit 10 (C * Real.exp (r * t)) = d}).toReal / T)
      Filter.atTop (nhds (benfordProb 10 d)) := by
  have hL0 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  set s := r / Real.log 10 with hs_def
  have hs : s ≠ 0 := div_ne_zero hr hL0.ne'
  set c := Real.logb 10 C
  set α := Real.logb 10 d
  set β := Real.logb 10 (d + 1)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hα : 0 ≤ α := Real.logb_nonneg (by norm_num) (by exact_mod_cast hd1)
  have hαβ : α ≤ β := Real.logb_le_logb_of_le (by norm_num) hd0 (by linarith)
  have hβ : β ≤ 1 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_one]
    have : (d : ℝ) ≤ 9 := by exact_mod_cast hd9
    linarith
  let h : ℝ → ℝ := fun u => (Set.Ico α β).indicator (1 : ℝ → ℝ) (Int.fract u)
  let g : ℝ → ℝ := fun t => h (s * t + c)
  have hlog : ∀ t, Real.logb 10 (C * Real.exp (r * t)) = s * t + c := by
    intro t
    rw [Real.logb_mul hC.ne' (Real.exp_pos _).ne']
    simp only [c, s, Real.logb, Real.log_exp]
    ring
  have hfm : Measurable fun u : ℝ => Int.fract u := measurable_fract
  have hhm : Measurable h := (measurable_one.indicator measurableSet_Ico).comp hfm
  have hgm : Measurable g := hhm.comp ((measurable_id.const_mul s).add_const c)
  set A : Set ℝ := {t | Int.fract (s * t + c) ∈ Set.Ico α β}
  have hAm : MeasurableSet A :=
    (hfm.comp ((measurable_id.const_mul s).add_const c)) measurableSet_Ico
  have hgA : g = A.indicator 1 := by
    funext t
    simp only [g, h, A, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
  -- the volume as an interval integral
  have hvol : ∀ T, 0 ≤ T →
      (volume {t : ℝ | t ∈ Set.Icc 0 T ∧ leadingDigit 10 (C * Real.exp (r * t)) = d}).toReal =
        ∫ t in (0 : ℝ)..T, g t := by
    intro T hT
    have hset : {t : ℝ | t ∈ Set.Icc 0 T ∧ leadingDigit 10 (C * Real.exp (r * t)) = d} =
        A ∩ Set.Icc 0 T := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, A, leadingDigit_eq_iff_aux' _ d hd1, hlog]
      tauto
    rw [hset, intervalIntegral.integral_of_le hT, hgA, integral_indicator_one hAm,
      Measure.real, Measure.restrict_apply hAm]
    congr 1
    exact measure_congr (Filter.EventuallyEq.inter (Filter.EventuallyEq.refl _ _) Ioc_ae_eq_Icc).symm
  -- periodicity
  have hh1 : Function.Periodic h 1 := fun u => by simp only [h, Int.fract_add_one]
  set P := |s|⁻¹ with hP
  have hPpos : 0 < P := inv_pos.mpr (abs_pos.mpr hs)
  have hsP : s * P = 1 ∨ s * P = -1 := by
    rcases lt_or_gt_of_ne hs with h' | h'
    · right; rw [hP, abs_of_neg h']; field_simp
    · left; rw [hP, abs_of_pos h']; field_simp
  have hgP : Function.Periodic g P := by
    intro t
    simp only [g]
    rw [show s * (t + P) + c = (s * t + c) + s * P by ring]
    rcases hsP with h' | h'
    · rw [h']; exact hh1 _
    · rw [h']; exact hh1.neg _
  -- integral over one period
  have hY : ∫ t in (0 : ℝ)..P, g t = (β - α) * P := by
    have := intervalIntegral.integral_comp_mul_add (f := h) (a := 0) (b := P) hs c
    simp only [g]
    rw [this, mul_zero, zero_add, smul_eq_mul]
    rcases lt_or_gt_of_ne hs with h' | h'
    · have e : s * P = -1 := by rw [hP, abs_of_neg h']; field_simp
      have key := hh1.intervalIntegral_add_eq (-1 + c) 0
      rw [show -1 + c + 1 = c by ring, zero_add, fract_indicator_integral α β hα hαβ hβ] at key
      rw [e, intervalIntegral.integral_symm, key, hP, abs_of_neg h']
      field_simp
    · have e : s * P = 1 := by rw [hP, abs_of_pos h']; field_simp
      have key := hh1.intervalIntegral_add_eq c 0
      rw [add_comm c 1, zero_add, fract_indicator_integral α β hα hαβ hβ] at key
      rw [e, key, hP, abs_of_pos h']
      field_simp
  have hgint : IntervalIntegrable g volume 0 P := by
    refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun hgm.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun t => ?_
    simp only [g, h, Real.norm_eq_abs]
    rw [abs_one]
    by_cases hm : Int.fract (s * t + c) ∈ Set.Ico α β <;> simp [hm]
  obtain hlo := fun T => hgP.sInf_add_zsmul_le_integral_of_pos hgint hPpos T
  obtain hhi := fun T => hgP.integral_le_sSup_add_zsmul_of_pos hgint hPpos T
  set m1 := sInf ((fun t => ∫ x in (0 : ℝ)..t, g x) '' Set.Icc 0 P)
  set m2 := sSup ((fun t => ∫ x in (0 : ℝ)..t, g x) '' Set.Icc 0 P)
  rw [hY] at hlo hhi
  have htarget : benfordProb 10 d = β - α := by
    rw [benfordProb, ← Real.logb_div (by positivity) hd0.ne']
    congr 1
    field_simp
  rw [htarget]
  have hY0 : 0 ≤ β - α := by linarith
  have hlim1 : Filter.Tendsto (fun T : ℝ => (m1 - (β - α) * P) / T + (β - α)) Filter.atTop
      (nhds (β - α)) := by
    simpa using (tendsto_const_nhds.div_atTop Filter.tendsto_id).add
      (tendsto_const_nhds (x := β - α))
  have hlim2 : Filter.Tendsto (fun T : ℝ => m2 / T + (β - α)) Filter.atTop (nhds (β - α)) := by
    simpa using (tendsto_const_nhds.div_atTop Filter.tendsto_id).add
      (tendsto_const_nhds (x := β - α))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim1 hlim2 ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop 0] with T hT
    rw [hvol T hT.le, le_div_iff₀ hT]
    have h1 := hlo T
    have hfl : T / P - 1 ≤ (⌊T / P⌋ : ℝ) := by linarith [Int.lt_floor_add_one (T / P)]
    rw [zsmul_eq_mul] at h1
    have : (m1 - (β - α) * P) / T * T = m1 - (β - α) * P := by field_simp
    have h2 : (T / P - 1) * ((β - α) * P) = (β - α) * T - (β - α) * P := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right hfl (mul_nonneg hY0 hPpos.le)]
  · filter_upwards [Filter.eventually_gt_atTop 0] with T hT
    rw [hvol T hT.le, div_le_iff₀ hT]
    have h1 := hhi T
    have hfl : (⌊T / P⌋ : ℝ) ≤ T / P := Int.floor_le _
    rw [zsmul_eq_mul] at h1
    have : m2 / T * T = m2 := by field_simp
    have h2 : (T / P) * ((β - α) * P) = (β - α) * T := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right hfl (mul_nonneg hY0 hPpos.le)]
