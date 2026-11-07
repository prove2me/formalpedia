-- Prove2me | solution 1 for AvramDividend.Classical.avram_f15_original_sigma_family_stopped_future_exponential_unit_condexp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:13:59.679649+00:00
-- url     : https://prove2.me/submissions/3b7f62f4-4e32-4787-ba55-dc571ca5bda2

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f14_original_sigma_family_bounded_and_preruin
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_compensated_exponential_unit_condExp

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∀ k,
      Integrable (fun ω => Real.exp
        (θ * (X.X (σ k ω + h) ω - X.X (σ k ω) ω) -
          (h : ℝ) * X.ψ θ)) P ∧
      (P[(fun ω => Real.exp
        (θ * (X.X (σ k ω + h) ω - X.X (σ k ω) ω) -
          (h : ℝ) * X.ψ θ)) |
          (hσstop k).measurableSpace] =ᵐ[P] (fun _ => (1 : ℝ))) := by
  intro k
  have hbounded : ∀ ω, σ k ω ≤ (n : ℝ≥0) := by
    intro ω
    exact (avram_p4_f14_original_sigma_family_bounded_and_preruin
      X x D n τ hτeq σ hσle k ω).1
  have hEvents : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s]
      {ω : Ω | σ k ω ≤ s} := by
    intro s
    simpa only [WithTop.coe_le_coe] using (hσstop k s)
  simpa only [] using
    (avram_wave6_03_original_rightCont_stopped_compensated_exponential_unit_condExp
      X (σ k) hEvents n hbounded h θ hθ)
