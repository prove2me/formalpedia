-- Prove2me | solution 1 for AvramDividend.Classical.independence_of_pointwise_limit_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T17:41:24.549041+00:00
-- url     : https://prove2.me/submissions/5fd4ef76-1384-4443-b795-a8bc279ef32e

import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory ProbabilityTheory Filter Topology

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (Z : ℕ → Ω → ℝ) (z : Ω → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hz : Measurable z)
    (hi : ∀ n, Indep (MeasurableSpace.comap (Z n) inferInstance) m P)
    (ht : ∀ ω, Tendsto (fun n => Z n ω) atTop (𝓝 (z ω))) :
    Indep (MeasurableSpace.comap z inferInstance) m P := by
  have hzΩ : Measurable[mΩ] z := hz.mono hm le_rfl
  have hZΩ (n : ℕ) : Measurable[mΩ] (Z n) := (hZ n).mono hm le_rfl
  apply (indep_comap_of_bcf hm hzΩ.aemeasurable ?_).symm
  intro A hA f
  have heq (n : ℕ) :
      (∫ ω in A, f (Z n ω) ∂P) =
        P.real A * (∫ ω, f (Z n ω) ∂P) := by
    exact (hi n).symm.setIntegral_eq_mul hm (hZΩ n).aemeasurable hA
      f.continuous.measurable.aestronglyMeasurable
  have hlim (ω : Ω) :
      Tendsto (fun n => f (Z n ω)) atTop (𝓝 (f (z ω))) :=
    f.continuous.continuousAt.tendsto.comp (ht ω)
  have hAint :
      Tendsto (fun n => ∫ ω in A, f (Z n ω) ∂P) atTop
        (𝓝 (∫ ω in A, f (z ω) ∂P)) := by
    haveI : IsFiniteMeasure (P.restrict A) := inferInstance
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
    · intro n
      exact (f.continuous.measurable.comp (hZΩ n)).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact ae_of_all _ (fun ω => f.norm_coe_le_norm (Z n ω))
    · exact ae_of_all _ hlim
  have hPint :
      Tendsto (fun n => ∫ ω, f (Z n ω) ∂P) atTop
        (𝓝 (∫ ω, f (z ω) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
    · intro n
      exact (f.continuous.measurable.comp (hZΩ n)).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact ae_of_all _ (fun ω => f.norm_coe_le_norm (Z n ω))
    · exact ae_of_all _ hlim
  have hfun :
      (fun n => ∫ ω in A, f (Z n ω) ∂P) =
      (fun n => P.real A * (∫ ω, f (Z n ω) ∂P)) :=
    funext heq
  rw [hfun] at hAint
  exact tendsto_nhds_unique hAint (tendsto_const_nhds.mul hPint)
