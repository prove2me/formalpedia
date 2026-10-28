-- Prove2me | solution 1 for AvramDividend.Classical.finiteMeasures_eq_of_complexMGF_eq_on_real_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T14:41:44.166989+00:00
-- url     : https://prove2.me/submissions/229b76ad-8d39-49a8-9a5c-eb53f38dbdfb

import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.NhdsWithin
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Finset Real Complex
open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

theorem solution
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (b : ℝ) (hb : b < 0)
    (hμ : AnalyticOnNhd ℂ (ProbabilityTheory.complexMGF id μ)
      {z : ℂ | b < z.re})
    (hν : AnalyticOnNhd ℂ (ProbabilityTheory.complexMGF id ν)
      {z : ℂ | b < z.re})
    (hreal : ∀ t : ℝ, b < t →
      ProbabilityTheory.complexMGF id μ (t : ℂ) =
      ProbabilityTheory.complexMGF id ν (t : ℂ)) :
    μ = ν := by
  have hU : IsPreconnected {z : ℂ | b < z.re} :=
    (convex_halfSpace_re_gt b).isPreconnected
  have h0 : (0 : ℂ) ∈ {z : ℂ | b < z.re} := by simpa using hb
  have htend : Tendsto (fun t : ℝ => (t : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => (t : ℂ))
        (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
      exact ne_of_gt ht
  have hev : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      ProbabilityTheory.complexMGF id μ (t : ℂ) =
      ProbabilityTheory.complexMGF id ν (t : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hreal t (lt_trans hb (Set.mem_Ioi.1 ht))
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ),
      ProbabilityTheory.complexMGF id μ z =
      ProbabilityTheory.complexMGF id ν z :=
    htend.frequently hev.frequently
  have heq := hμ.eqOn_of_preconnected_of_frequently_eq hν hU h0 hfreq
  apply Measure.ext_of_charFun
  funext t
  rw [← ProbabilityTheory.complexMGF_id_mul_I,
      ← ProbabilityTheory.complexMGF_id_mul_I]
  apply heq
  simpa using hb
