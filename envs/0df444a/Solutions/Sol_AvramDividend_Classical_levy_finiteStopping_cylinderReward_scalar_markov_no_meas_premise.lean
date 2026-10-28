-- Prove2me | solution 1 for AvramDividend.Classical.levy_finiteStopping_cylinderReward_scalar_markov_no_meas_premise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:37:00.913375+00:00
-- url     : https://prove2.me/submissions/77c95b1f-8958-4130-9364-ee798b14047f

import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Constructions
import Mathlib.MeasureTheory.Constructions.Pi
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_scalar_markov_no_meas_premise

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Finite-dimensional Lévy strong-Markov cylinder integrals have automatic stopped measurability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (J : Finset ℝ≥0)
    (h : (J → ℝ) → ℝ≥0∞)
    (hh : Continuous h) (hhm : Measurable h)
    (C : ℝ≥0∞) (hbound : ∀ z, h z ≤ C)
    (hfin : (∫⁻ _ : Ω, C ∂P) ≠ ∞) :
    (∫⁻ ω, Set.indicator A
      (fun ω' : Ω => h (fun j : J =>
        X.X (τ ω' + (j : ℝ≥0)) ω' - X.X (τ ω') ω')) ω ∂P) =
    P A * (∫⁻ y, h (fun j : J => y (j : ℝ≥0))
      ∂(Measure.map
        (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
  let proj : (ℝ≥0 → ℝ) → (J → ℝ) :=
    fun y j => y (j : ℝ≥0)
  have hpCont : Continuous proj := by
    apply continuous_pi
    intro j
    exact continuous_apply (j : ℝ≥0)
  have hpMeas : Measurable proj := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pi_apply (j : ℝ≥0)
  let g : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun y => h (proj y)
  have hg : Continuous g := hh.comp hpCont
  have hgm : Measurable g := hhm.comp hpMeas
  have hgBound : ∀ y, g y ≤ C := fun y => hbound (proj y)
  simpa only [g, proj] using
    (levy_finiteStopping_scalar_markov_no_meas_premise
      X τ hstop A hA g hg hgm C hgBound hfin)
