-- Prove2me | solution 1 for CachonPushPull.Pareto.push_retailer_increasing
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:13:13.27718+00:00
-- url     : https://prove2.me/submissions/14937471-2941-4a7c-85ef-7b48a96ac7b3

import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

lemma aux_pri_eq (μ : Measure ℝ) (p v q : ℝ) :
    pushRetailerProfit μ p v q = (p - v) * (cdf μ q * q - ∫ x in (0 : ℝ)..q, cdf μ x) := by
  unfold pushRetailerProfit pushRetailerProfitAt pushPrice S
  ring

lemma aux_pri_ii (μ : Measure ℝ) (a b : ℝ) :
    IntervalIntegrable (fun x => cdf μ x) volume a b :=
  (cdf μ).mono.intervalIntegrable

lemma aux_pri_bound (μ : Measure ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, cdf μ x) ≤ (b - a) * cdf μ b := by
  have h := intervalIntegral.integral_mono_on hab (aux_pri_ii μ a b)
    (intervalIntegrable_const (c := cdf μ b)) (fun x hx => (cdf μ).mono hx.2)
  simpa [intervalIntegral.integral_const, smul_eq_mul] using h

end CachonPushPull.Pareto

open CachonPushPull.Pareto
open MeasureTheory ProbabilityTheory

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) :
    (∀ q : ℝ, 0 < q → HasDerivAt (pushRetailerProfit μ p v) ((p - v) * f q * q) q) ∧
    StrictMonoOn (pushRetailerProfit μ p v) (Set.Ici 0) := by
  have hfun : pushRetailerProfit μ p v =
      fun q => (p - v) * (cdf μ q * q - ∫ x in (0 : ℝ)..q, cdf μ x) := by
    funext q; exact aux_pri_eq μ p v q
  have hpv : 0 < p - v := by linarith
  refine ⟨?_, ?_⟩
  · intro q hq
    rw [hfun]
    have hF := hD.hasDerivAt q hq
    have hint : HasDerivAt (fun u => ∫ x in (0 : ℝ)..u, cdf μ x) (cdf μ q) q :=
      intervalIntegral.integral_hasDerivAt_right (aux_pri_ii μ 0 q)
        ((cdf μ).mono.measurable.stronglyMeasurable.stronglyMeasurableAtFilter)
        hF.continuousAt
    have h2 : HasDerivAt (fun u => (p - v) * (cdf μ u * u - ∫ x in (0 : ℝ)..u, cdf μ x))
        ((p - v) * (f q * q + cdf μ q * 1 - cdf μ q)) q := by
      have h0 := (hF.mul (hasDerivAt_id' q)).sub hint
      exact h0.const_mul (p - v)
    exact h2.congr_deriv (by ring)
  · intro a ha b hb hab
    simp only [Set.mem_Ici] at ha hb
    rw [aux_pri_eq, aux_pri_eq]
    apply mul_lt_mul_of_pos_left _ hpv
    set m := (a + b) / 2 with hm
    have ham : a ≤ m := by rw [hm]; linarith
    have hmb : m < b := by rw [hm]; linarith
    have hm0 : 0 < m := by rw [hm]; linarith
    have hsplit : (∫ x in (0 : ℝ)..b, cdf μ x) =
        (∫ x in (0 : ℝ)..a, cdf μ x) + (∫ x in a..m, cdf μ x) + (∫ x in m..b, cdf μ x) := by
      rw [intervalIntegral.integral_add_adjacent_intervals (aux_pri_ii μ 0 a) (aux_pri_ii μ a m),
        intervalIntegral.integral_add_adjacent_intervals (aux_pri_ii μ 0 m) (aux_pri_ii μ m b)]
    have hb1 := aux_pri_bound μ ham
    have hb2 := aux_pri_bound μ hmb.le
    have hFmb : cdf μ m < cdf μ b := hD.strictMonoOn (Set.mem_Ici.mpr hm0.le)
      (Set.mem_Ici.mpr hb) hmb
    have hFam : cdf μ a ≤ cdf μ m := (cdf μ).mono ham
    rw [hsplit]
    nlinarith [mul_lt_mul_of_pos_left hFmb hm0, mul_le_mul_of_nonneg_left hFam ha]
