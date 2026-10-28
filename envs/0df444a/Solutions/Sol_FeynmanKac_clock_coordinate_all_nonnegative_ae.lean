-- Prove2me | solution 1 for FeynmanKac.clock_coordinate_all_nonnegative_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T09:21:16.099268+00:00
-- url     : https://prove2.me/submissions/397cf478-7c90-4e6d-a655-ebfe408fc73a

import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Theorems.Thm_FunctionalInequalities_Probability_Diffusion_IsDiffusion_ae_linear_eq_integral_readable
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P) :
    ∀ᵐ ω ∂P, ∀ (u : ℝ), 0 ≤ u →
      m.augmentedPath u ω (1 : Fin 2) = m.initialTime + u := by
  let ℓ : (Fin 2 → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (1 : Fin 2)
  have hnoise : ∀ z (k : Fin 1), ℓ (m.augmentedVolatility z k) = 0 := by
    intro z k
    have hk : k = (0 : Fin 1) := Subsingleton.elim k 0
    subst k
    simpa [ℓ] using m.augmentedVolatility_clock z
  obtain ⟨B, hbB⟩ := m.augmentedDrift_bounded
  have hcore :=
    FunctionalInequalities.Probability.Diffusion.IsDiffusion.ae_linear_eq_integral_readable
      m.augmentedDrift_continuous hbB m.isDiffusion ℓ hnoise
  filter_upwards [hcore] with ω hω
  intro u hu
  have hωu := hω u hu
  have hintegrand :
      (fun s => ℓ (m.augmentedDrift (m.augmentedPath s ω))) =
        (fun _ => (1 : ℝ)) := by
    funext s
    simp [ℓ, m.augmentedDrift_clock]
  rw [hintegrand] at hωu
  simpa [ℓ, m.initialCoordinates_clock, MeasureTheory.integral_const,
    Real.volume_real_Ioc_of_le hu] using hωu
