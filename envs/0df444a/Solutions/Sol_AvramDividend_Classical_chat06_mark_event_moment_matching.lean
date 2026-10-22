-- Prove2me | solution 1 for AvramDividend.Classical.chat06_mark_event_moment_matching
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:59:41.560998+00:00
-- url     : https://prove2.me/submissions/b412c077-493b-4543-8a1a-ac359a262b81

import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Real

namespace AvramChat06

/-- Given fixed-length mark moments and independence between the count
and each fixed-length mark sum, the two candidate Laplace integrands
have exactly equal expectations on every event {N=k}. -/
theorem mark_event_moment_matching
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N)
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, Measurable (Y i))
    (hIndep : ∀ k : ℕ,
      IndepFun N (fun ω => ∑ i ∈ Finset.range k, Y i ω) P)
    (θ m : ℝ)
    (hFixed : ∀ k : ℕ,
      (∫ ω, Real.exp (θ * ∑ i ∈ Finset.range k, Y i ω) ∂P) =
        m ^ k)
    (k : ℕ) :
    (∫ ω in {ω | N ω = k},
      Real.exp (θ * ∑ i ∈ Finset.range (N ω), Y i ω) ∂P) =
    (∫ ω in {ω | N ω = k}, m ^ (N ω) ∂P) := by
  let S : Set Ω := {ω | N ω = k}
  have hs : MeasurableSet S := hN (measurableSet_singleton k)
  have hsum : Measurable (fun ω => ∑ i ∈ Finset.range k, Y i ω) :=
    Finset.measurable_sum _ fun i _ => hY i
  have hf : Measurable (fun n : ℕ => if n = k then (1 : ℝ) else 0) :=
    measurable_of_countable _
  have hg : Measurable (fun z : ℝ => Real.exp (θ * z)) := by fun_prop
  have hi : IndepFun
      (fun ω => if N ω = k then (1 : ℝ) else 0)
      (fun ω => Real.exp (θ * ∑ i ∈ Finset.range k, Y i ω)) P := by
    simpa only [Function.comp_def] using (hIndep k).comp hf hg
  have hproduct := hi.integral_mul_eq_mul_integral
    (hf.comp hN).aestronglyMeasurable
    (hg.comp hsum).aestronglyMeasurable
  have hprob :
      (∫ ω, (if N ω = k then (1 : ℝ) else 0) ∂P) = P.real S := by
    have hEq :
        (fun ω => if N ω = k then (1 : ℝ) else 0) =
          S.indicator fun _ => (1 : ℝ) := by
      funext ω
      by_cases hk : N ω = k <;> simp [S, Set.indicator_apply, hk]
    rw [hEq, integral_indicator_const (1 : ℝ) hs]
    simp
  have hfixedEvent :
      (∫ ω in S,
        Real.exp (θ * ∑ i ∈ Finset.range k, Y i ω) ∂P) =
      P.real S * m ^ k := by
    rw [← integral_indicator hs]
    have hEq :
        S.indicator
          (fun ω => Real.exp (θ * ∑ i ∈ Finset.range k, Y i ω)) =
        fun ω => (if N ω = k then (1 : ℝ) else 0) *
          Real.exp (θ * ∑ i ∈ Finset.range k, Y i ω) := by
      funext ω
      by_cases hk : N ω = k <;>
        simp [S, Set.indicator_apply, hk]
    have hp' :
        (∫ ω, (if N ω = k then (1 : ℝ) else 0) *
          Real.exp (θ * ∑ i ∈ Finset.range k, Y i ω) ∂P) =
        (∫ ω, (if N ω = k then (1 : ℝ) else 0) ∂P) *
          ∫ ω, Real.exp (θ * ∑ i ∈ Finset.range k, Y i ω) ∂P := by
      simpa only [Pi.mul_apply] using hproduct
    rw [hEq, hp', hprob, hFixed k]
  have hleft :
      (∫ ω in S,
        Real.exp (θ * ∑ i ∈ Finset.range (N ω), Y i ω) ∂P) =
      (∫ ω in S,
        Real.exp (θ * ∑ i ∈ Finset.range k, Y i ω) ∂P) := by
    apply setIntegral_congr_fun hs
    intro ω hw
    change N ω = k at hw
    change Real.exp (θ * ∑ i ∈ Finset.range (N ω), Y i ω) =
      Real.exp (θ * ∑ i ∈ Finset.range k, Y i ω)
    rw [hw]
  have hright :
      (∫ ω in S, m ^ (N ω) ∂P) =
      P.real S * m ^ k := by
    have heq : Set.EqOn
        (fun ω => m ^ (N ω)) (fun _ => m ^ k) S := by
      intro ω hw
      change N ω = k at hw
      change m ^ (N ω) = m ^ k
      rw [hw]
    rw [setIntegral_congr_fun hs heq]
    rw [integral_const]
    simp [smul_eq_mul]
  change (∫ ω in S,
      Real.exp (θ * ∑ i ∈ Finset.range (N ω), Y i ω) ∂P) =
    (∫ ω in S, m ^ (N ω) ∂P)
  rw [hleft, hfixedEvent, hright]

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (N : Ω → ℕ) (hN : Measurable N)
    (Y : ℕ → Ω → ℝ) (hY : ∀ i, Measurable (Y i))
    (hIndep : ∀ k : ℕ,
      IndepFun N (fun ω => ∑ i ∈ Finset.range k, Y i ω) P)
    (θ m : ℝ)
    (hFixed : ∀ k : ℕ,
      (∫ ω, Real.exp (θ * ∑ i ∈ Finset.range k, Y i ω) ∂P) = m ^ k)
    (k : ℕ) :
    (∫ ω in {ω | N ω = k},
      Real.exp (θ * ∑ i ∈ Finset.range (N ω), Y i ω) ∂P) =
    (∫ ω in {ω | N ω = k}, m ^ (N ω) ∂P) := by
  exact mark_event_moment_matching N hN Y hY hIndep θ m hFixed k
