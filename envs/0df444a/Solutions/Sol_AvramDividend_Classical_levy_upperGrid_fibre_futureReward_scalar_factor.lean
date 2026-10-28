-- Prove2me | solution 1 for AvramDividend.Classical.levy_upperGrid_fibre_futureReward_scalar_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:44:33.260722+00:00
-- url     : https://prove2.me/submissions/0b727c72-033c-43b6-8c4d-ed49c70b166f

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_stoppedHistory_upperGrid_futureReward_product
import Theorems.Thm_AvramDividend_Classical_stoppedEvent_upperGridFibre_measurable
import Theorems.Thm_AvramDividend_Classical_productIndicator_futureReward_lintegral_factor
import Theorems.Thm_AvramDividend_Classical_realIndicator_pushforward_one_mass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

/-- Each stopped-time grid fibre factors its future-path reward against its event mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (τn : ℕ → Ω → ℝ≥0)
    (habove : ∀ ω n, τ ω ≤ τn n ω)
    (hfibres : ∀ n s,
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (n : ℕ) (s : ℝ≥0)
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω, Set.indicator (A ∩ {ω' : Ω | τn n ω' = s})
      (fun ω' => g (fun t : ℝ≥0 =>
        X.X (s + t) ω' - X.X s ω')) ω ∂P) =
    P (A ∩ {ω : Ω | τn n ω = s}) *
      (∫⁻ y, g y ∂(Measure.map
        (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
  let F : Set Ω := A ∩ {ω : Ω | τn n ω = s}
  let ν : Measure (ℝ≥0 → ℝ) :=
    Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P
  let μ : Measure ℝ :=
    Measure.map (Set.indicator F (fun _ : Ω => (1 : ℝ))) P
  have hF : MeasurableSet F :=
    (𝓕.le s F) (stoppedEvent_upperGridFibre_measurable
      τ A hA τn habove hfibres n s)
  have hf : Measurable
      (fun p : ℝ × (ℝ≥0 → ℝ) =>
        if p.1 = 1 then g p.2 else 0) :=
    (hg.comp measurable_snd).ite
      (measurableSet_eq_fun measurable_fst measurable_const) measurable_const
  have hproduct :=
    levy_stoppedHistory_upperGrid_futureReward_product
      (ι := Unit) X τ A hA τn habove hfibres n
      (fun _ : Unit => s)
      (fun _ : Unit => fun p : ℝ × (ℝ≥0 → ℝ) =>
        if p.1 = 1 then g p.2 else 0)
      (fun _ => hf)
  have hone :
      (∫⁻ ω, (if Set.indicator F (fun _ : Ω => (1 : ℝ)) ω = 1
        then g (fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)
        else 0) ∂P) =
      (∫⁻ h : ℝ, ∫⁻ y : (ℝ≥0 → ℝ),
        (if h = 1 then g y else 0) ∂ν ∂μ) := by
    simpa [F, μ, ν] using hproduct
  have heq (ω : Ω) :
      (if Set.indicator F (fun _ : Ω => (1 : ℝ)) ω = 1
        then g (fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)
        else 0) =
      Set.indicator F
        (fun ω' => g (fun t : ℝ≥0 =>
          X.X (s + t) ω' - X.X s ω')) ω := by
    by_cases hw : ω ∈ F
    · simp [Set.indicator, hw]
    · simp [Set.indicator, hw]
  change (∫⁻ ω, Set.indicator F
      (fun ω' => g (fun t : ℝ≥0 =>
        X.X (s + t) ω' - X.X s ω')) ω ∂P) =
    P F * (∫⁻ y, g y ∂ν)
  calc
    _ = ∫⁻ ω, (if Set.indicator F (fun _ : Ω => (1 : ℝ)) ω = 1
      then g (fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)
      else 0) ∂P := by
        apply lintegral_congr
        intro ω
        exact (heq ω).symm
    _ = ∫⁻ h : ℝ, ∫⁻ y : (ℝ≥0 → ℝ),
        (if h = 1 then g y else 0) ∂ν ∂μ := hone
    _ = P F * (∫⁻ y, g y ∂ν) := by
      rw [productIndicator_futureReward_lintegral_factor μ ν g hg]
      rw [realIndicator_pushforward_one_mass P F hF]
