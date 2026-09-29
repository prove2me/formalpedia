-- Prove2me | solution 1 for BanditAlgorithm.pmSignalMeasure_eq_symmetric_perturbation_of_fiber_sum
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T19:49:13.417217+00:00
-- url     : https://prove2.me/submissions/3ce28cf4-0961-4cdd-ae26-3da9c24dd282

import Definitions.Def_PartialMonitoringStochastic
import Mathlib.Data.ENNReal.BigOperators

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BanditAlgorithm

private lemma pmSignalMeasure_real_apply
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (w : Fin d → ℝ)
    (hw : w ∈ stdSimplex ℝ (Fin d)) (c : Fin k)
    (s : Set 𝕊) (hs : MeasurableSet s) :
    (pmSignalMeasure G w c).real s =
      ∑ i, s.indicator (fun _ => w i) (G.Φ c i) := by
  classical
  rw [Measure.real, pmSignalMeasure, Measure.map_apply
    (measurable_of_countable _) hs, pmOutcomeMeasure,
    Measure.sum_apply _ ((measurable_of_countable _) hs)]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
    Set.indicator, Set.mem_preimage, Pi.one_apply, tsum_fintype]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    split <;> simp [ENNReal.toReal_ofReal, hw.1]
  · intro i hi
    split <;> simp

theorem _root_.solution
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    [DecidableEq 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (c : Fin k)
    (u q : Fin d → ℝ) (Δ : ℝ)
    (hminus : (fun i => u i - Δ * q i) ∈ stdSimplex ℝ (Fin d))
    (hplus : (fun i => u i + Δ * q i) ∈ stdSimplex ℝ (Fin d))
    (hfiber : ∀ σ : 𝕊,
      ∑ i ∈ Finset.univ.filter (fun i => G.Φ c i = σ), q i = 0) :
    pmSignalMeasure G (fun i => u i - Δ * q i) c =
      pmSignalMeasure G (fun i => u i + Δ * q i) c := by
  classical
  let wm : Fin d → ℝ := fun i => u i - Δ * q i
  let wp : Fin d → ℝ := fun i => u i + Δ * q i
  letI : IsProbabilityMeasure (pmSignalMeasure G wm c) :=
    pmSignalMeasure_isProbabilityMeasure G wm hminus c
  letI : IsProbabilityMeasure (pmSignalMeasure G wp c) :=
    pmSignalMeasure_isProbabilityMeasure G wp hplus c
  ext s hs
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top (pmSignalMeasure G wm c) s)
    (measure_ne_top (pmSignalMeasure G wp c) s)).mp
  change (pmSignalMeasure G wm c).real s = (pmSignalMeasure G wp c).real s
  rw [pmSignalMeasure_real_apply G wm hminus c s hs,
    pmSignalMeasure_real_apply G wp hplus c s hs]
  simp only [Set.indicator_apply]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have hqset :
      ∑ i ∈ Finset.univ.filter (fun i => G.Φ c i ∈ s), q i = 0 := by
    have hpartition := Finset.sum_fiberwise_eq_sum_filter Finset.univ
      (Finset.univ.filter fun σ : 𝕊 => σ ∈ s) (G.Φ c) q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpartition
    rw [← hpartition]
    apply Finset.sum_eq_zero
    intro σ hσ
    exact hfiber σ
  unfold wm wp
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hΔq : ∑ i ∈ Finset.univ.filter (fun i => G.Φ c i ∈ s), Δ * q i = 0 := by
    rw [← Finset.mul_sum, hqset, mul_zero]
  rw [hΔq]
  ring

end BanditAlgorithm
