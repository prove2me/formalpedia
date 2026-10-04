-- Prove2me | solution 1 for AvramDividend.Classical.finiteMeasures_eq_of_complexMGF_eq_on_real_Iio
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T00:35:03.939048+00:00
-- url     : https://prove2.me/submissions/78b20d2e-f7f9-48f7-9275-633d9f94a548

import Mathlib
open MeasureTheory Filter Finset Real Complex
open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

open MeasureTheory Filter Finset Real Complex in
theorem solution (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (b : ℝ) (hb : 0 < b)
    (hμ : AnalyticOnNhd ℂ (ProbabilityTheory.complexMGF id μ)
      {z : ℂ | z.re < b})
    (hν : AnalyticOnNhd ℂ (ProbabilityTheory.complexMGF id ν)
      {z : ℂ | z.re < b})
    (hreal : ∀ t : ℝ, t < b →
      ProbabilityTheory.complexMGF id μ (t : ℂ) =
        ProbabilityTheory.complexMGF id ν (t : ℂ)) :
    μ = ν := by
  have hU : IsPreconnected {z : ℂ | z.re < b} :=
    (convex_halfSpace_re_lt b).isPreconnected
  have h0 : (0 : ℂ) ∈ {z : ℂ | z.re < b} := by simpa using hb
  have htend : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[<] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
      exact ne_of_lt ht
  have hev : ∀ᶠ t : ℝ in 𝓝[<] (0 : ℝ),
      ProbabilityTheory.complexMGF id μ (t : ℂ) = ProbabilityTheory.complexMGF id ν (t : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hreal t (lt_trans (Set.mem_Iio.1 ht) hb)
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ),
      ProbabilityTheory.complexMGF id μ z = ProbabilityTheory.complexMGF id ν z :=
    htend.frequently hev.frequently
  have heq := hμ.eqOn_of_preconnected_of_frequently_eq hν hU h0 hfreq
  apply Measure.ext_of_charFun
  funext t
  rw [← ProbabilityTheory.complexMGF_id_mul_I, ← ProbabilityTheory.complexMGF_id_mul_I]
  apply heq
  simpa using hb
