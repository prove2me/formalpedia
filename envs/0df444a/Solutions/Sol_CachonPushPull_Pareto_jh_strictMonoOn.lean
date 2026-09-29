-- Prove2me | solution 1 for CachonPushPull.Pareto.jh_strictMonoOn
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:09:43.693718+00:00
-- url     : https://prove2.me/submissions/c7063fcb-7740-44d0-8422-68692c8feb03

import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Model

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

lemma aux_jhsm_cdf_lt_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (q : ℝ) (hq : 0 ≤ q) : cdf μ q < 1 := by
  have h1 : cdf μ q < cdf μ (q + 1) :=
    hD.strictMonoOn (Set.mem_Ici.mpr hq) (Set.mem_Ici.mpr (by linarith)) (by linarith)
  linarith [cdf_le_one μ (q + 1)]

lemma aux_jhsm_f_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (x : ℝ) (hx : 0 < x) : 0 ≤ f x :=
  (hD.hasDerivAt x hx).nonneg_of_monotone (monotone_cdf μ)

lemma aux_jhsm_g_strictMonoOn (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) :
    StrictMonoOn (fun y : ℝ => y * f y / (1 - cdf μ y)) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro x hx
    have hx' : (0 : ℝ) < x := hx
    have hne : deriv (fun y : ℝ => y * f y / (1 - cdf μ y)) x ≠ 0 := (hD.igfr x hx').ne'
    exact (differentiableAt_of_deriv_ne_zero hne).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact hD.igfr x hx

lemma aux_jhsm_S_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (q : ℝ) (hq : 0 < q) :
    S μ q = q * ∫ t in (0 : ℝ)..1, (1 - cdf μ (q * t)) := by
  have hint : IntervalIntegrable (cdf μ) volume 0 q := (monotone_cdf μ).intervalIntegrable
  have h1 : ∫ x in (0 : ℝ)..q, (1 - cdf μ x) = q - ∫ x in (0 : ℝ)..q, cdf μ x := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hint]
    simp
  have h2 : ∫ t in (0 : ℝ)..1, (1 - cdf μ (q * t)) =
      q⁻¹ • ∫ x in q * 0..q * 1, (1 - cdf μ x) :=
    intervalIntegral.integral_comp_mul_left (fun x => 1 - cdf μ x) hq.ne'
  rw [h2, mul_zero, mul_one, h1, smul_eq_mul, S]
  field_simp

lemma aux_jhsm_ratio_mono (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    MonotoneOn (fun q : ℝ => (1 - cdf μ (t * q)) / (1 - cdf μ q)) (Set.Ioi 0) := by
  have hderiv : ∀ q : ℝ, 0 < q → HasDerivAt (fun q : ℝ => (1 - cdf μ (t * q)) / (1 - cdf μ q))
      (((0 - f (t * q)) * (t * 1) * (1 - cdf μ q) - (1 - cdf μ (t * q)) * (0 - f q))
        / (1 - cdf μ q) ^ 2) q := by
    intro q hq
    have htq : 0 < t * q := mul_pos ht0 hq
    have hA : HasDerivAt (fun q : ℝ => 1 - cdf μ (t * q)) ((0 - f (t * q)) * (t * 1)) q := by
      have := ((hasDerivAt_const (t * q) (1 : ℝ)).sub (hD.hasDerivAt (t * q) htq)).comp q
        ((hasDerivAt_id q).const_mul t)
      simpa [Function.comp_def] using this
    have hB : HasDerivAt (fun q : ℝ => 1 - cdf μ q) (0 - f q) q :=
      (hasDerivAt_const q (1 : ℝ)).sub (hD.hasDerivAt q hq)
    have hne : (1 - cdf μ q) ≠ 0 := by
      have := aux_jhsm_cdf_lt_one μ f hD q hq.le
      linarith
    exact hA.div hB hne
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro q hq
    exact (hderiv q hq).continuousAt.continuousWithinAt
  · intro q hq
    rw [interior_Ioi] at hq
    exact (hderiv q hq).differentiableAt.differentiableWithinAt
  · intro q hq
    rw [interior_Ioi] at hq
    have hq' : (0 : ℝ) < q := hq
    rw [(hderiv q hq').deriv]
    apply div_nonneg _ (sq_nonneg _)
    have htq : 0 < t * q := mul_pos ht0 hq'
    have hu : 0 < 1 - cdf μ q := by
      have := aux_jhsm_cdf_lt_one μ f hD q hq'.le
      linarith
    have hut : 0 < 1 - cdf μ (t * q) := by
      have := aux_jhsm_cdf_lt_one μ f hD (t * q) htq.le
      linarith
    have hg : (t * q) * f (t * q) / (1 - cdf μ (t * q)) ≤ q * f q / (1 - cdf μ q) :=
      (aux_jhsm_g_strictMonoOn μ f hD).monotoneOn htq hq'
        (by nlinarith)
    rw [div_le_div_iff₀ hut hu] at hg
    -- hg : t*q*f(tq)*(1-F q) ≤ q * f q * (1 - F(tq))
    have key : t * f (t * q) * (1 - cdf μ q) ≤ f q * (1 - cdf μ (t * q)) := by
      have h' : q * (t * f (t * q) * (1 - cdf μ q)) ≤ q * (f q * (1 - cdf μ (t * q))) := by
        nlinarith
      exact le_of_mul_le_mul_left h' hq'
    nlinarith

lemma aux_jhsm_R_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (q : ℝ) (hq : 0 < q) :
    S μ q / (q * (1 - cdf μ q)) =
      ∫ t in (0 : ℝ)..1, (1 - cdf μ (q * t)) / (1 - cdf μ q) := by
  have hu : 0 < 1 - cdf μ q := by
    have := aux_jhsm_cdf_lt_one μ f hD q hq.le
    linarith
  rw [intervalIntegral.integral_div, aux_jhsm_S_eq μ q hq]
  field_simp

lemma aux_jhsm_int_ok (μ : Measure ℝ) [IsProbabilityMeasure μ] (q : ℝ) (hq : 0 ≤ q) :
    IntervalIntegrable (fun t => (1 - cdf μ (q * t)) / (1 - cdf μ q)) volume 0 1 := by
  have hanti : Antitone (fun t => 1 - cdf μ (q * t)) := by
    intro a b hab
    have : cdf μ (q * a) ≤ cdf μ (q * b) :=
      monotone_cdf μ (mul_le_mul_of_nonneg_left hab hq)
    simp only
    linarith
  exact hanti.intervalIntegrable.div_const _

lemma aux_jhsm_R_mono (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    S μ a / (a * (1 - cdf μ a)) ≤ S μ b / (b * (1 - cdf μ b)) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [aux_jhsm_R_eq μ f hD a ha, aux_jhsm_R_eq μ f hD b hb]
  apply intervalIntegral.integral_mono_on zero_le_one (aux_jhsm_int_ok μ a ha.le)
    (aux_jhsm_int_ok μ b hb.le)
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0
    simp only [mul_zero]
    have hua : 0 < 1 - cdf μ a := by
      have := aux_jhsm_cdf_lt_one μ f hD a ha.le
      linarith
    have hub : 0 < 1 - cdf μ b := by
      have := aux_jhsm_cdf_lt_one μ f hD b hb.le
      linarith
    have hmono : cdf μ a ≤ cdf μ b := monotone_cdf μ hab
    have h1 : 0 ≤ 1 - cdf μ 0 := by linarith [cdf_le_one μ 0]
    exact div_le_div_of_nonneg_left h1 hub (by linarith)
  · have := aux_jhsm_ratio_mono μ f hD t h0 ht.2 ha hb hab
    simpa [mul_comm] using this

lemma aux_jhsm_R_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (b : ℝ) (hb : 0 < b) :
    0 < S μ b / (b * (1 - cdf μ b)) := by
  have hub : 0 < 1 - cdf μ b := by
    have := aux_jhsm_cdf_lt_one μ f hD b hb.le
    linarith
  have h1 : ∫ t in (0 : ℝ)..1, (1 : ℝ) ≤
      ∫ t in (0 : ℝ)..1, (1 - cdf μ (b * t)) / (1 - cdf μ b) := by
    apply intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const
      (aux_jhsm_int_ok μ b hb.le)
    intro t ht
    rw [le_div_iff₀ hub, one_mul]
    have : cdf μ (b * t) ≤ cdf μ b := by
      apply monotone_cdf μ
      nlinarith [ht.1, ht.2]
    linarith
  rw [aux_jhsm_R_eq μ f hD b hb]
  rw [intervalIntegral.integral_const] at h1
  simp only [sub_zero, smul_eq_mul, mul_one] at h1
  linarith

end CachonPushPull.Pareto

open CachonPushPull.Pareto
open MeasureTheory ProbabilityTheory

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) :
    StrictMonoOn (fun q : ℝ => j μ q * hazard μ f q) (Set.Ioi 0) := by
  have hform : ∀ q : ℝ, 0 < q → j μ q * hazard μ f q =
      (S μ q / (q * (1 - cdf μ q))) * (q * f q / (1 - cdf μ q)) := by
    intro q hq
    have hu : 0 < 1 - cdf μ q := by
      have := aux_jhsm_cdf_lt_one μ f hD q hq.le
      linarith
    simp only [j, hazard]
    field_simp
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  simp only
  rw [hform a ha', hform b hb']
  have hR := aux_jhsm_R_mono μ f hD a b ha' hab.le
  have hRpos := aux_jhsm_R_pos μ f hD b hb'
  have hg : a * f a / (1 - cdf μ a) < b * f b / (1 - cdf μ b) :=
    aux_jhsm_g_strictMonoOn μ f hD ha hb hab
  have hga : 0 ≤ a * f a / (1 - cdf μ a) := by
    have hua : 0 < 1 - cdf μ a := by
      have := aux_jhsm_cdf_lt_one μ f hD a ha'.le
      linarith
    exact div_nonneg (mul_nonneg ha'.le (aux_jhsm_f_nonneg μ f hD a ha')) hua.le
  calc (S μ a / (a * (1 - cdf μ a))) * (a * f a / (1 - cdf μ a))
      ≤ (S μ b / (b * (1 - cdf μ b))) * (a * f a / (1 - cdf μ a)) :=
        mul_le_mul_of_nonneg_right hR hga
    _ < (S μ b / (b * (1 - cdf μ b))) * (b * f b / (1 - cdf μ b)) :=
        mul_lt_mul_of_pos_left hg hRpos
