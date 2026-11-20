-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_true_ruinclipped_interior_and_sameclock_fullmark_L2_kit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T15:56:08.596159+00:00
-- url     : https://prove2.me/submissions/16a96f71-7854-499f-98bd-12a5e53f35bb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_true_ruinclipped_subordinate_clock_positive_interior_before_contact_ae
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_stopped_uniform_L2_mean_and_energy_v2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hUBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (cut : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (n m : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (μ : Measure ℝ≥0) [SFinite μ] :
    (∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (t : ℝ≥0∞) < (ρ ω : ℝ≥0∞) →
        0 < riskProcess X x D t ω) ∧
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let grid : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℕ → ℝ := fun i =>
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    let H : ℕ → Ω → ℝ := fun i ω =>
      max (-K) (min K (Real.exp (-(q * (grid i : ℝ))) *
        deriv w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
          (grid i))))
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (if (ρ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H i ω) * ((N i ω).toReal - r i)
    MemLp (fun ω => ∑ i ∈ Finset.range m, Z i ω) 2 P ∧
    (∫ ω, ∑ i ∈ Finset.range m, Z i ω ∂P) = 0 ∧
    (∀ ω, ρ ω = 0 → ∑ i ∈ Finset.range m, Z i ω = 0) ∧
        Integrable (fun ω => ∑ i ∈ Finset.range m, (Z i ω)^2) P ∧
      (∫ ω, ∑ i ∈ Finset.range m, (Z i ω)^2 ∂P) =
        ∑ i ∈ Finset.range m,
          r i * ∫ ω, (if (ρ ω : WithTop ℝ≥0) ≤
            (grid i : WithTop ℝ≥0) then (0 : ℝ)
            else H i ω)^2 ∂P := by
  letI : IsProbabilityMeasure P := X.isProbability
  constructor
  · exact
      avram_pj_workerC_original_true_ruinclipped_subordinate_clock_positive_interior_before_contact_ae
        X hUBV x C D hD n hn τ ρ hτeq hρle μ
  · exact
      avram_pj_workerC_original_stopped_uniform_L2_mean_and_energy_v2
        X x D hD.1.1 w q K hK cut ρ hρstop n m hn
