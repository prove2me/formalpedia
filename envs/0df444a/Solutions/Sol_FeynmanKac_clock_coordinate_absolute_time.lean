-- Prove2me | solution 1 for FeynmanKac.clock_coordinate_absolute_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:03:41.686379+00:00
-- url     : https://prove2.me/submissions/66b3ec96-d3e3-451d-ba95-a59f3b881bd7

import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Theorems.Thm_FunctionalInequalities_Probability_Diffusion_IsDiffusion_ae_linear_eq_integral_readable
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- The second coordinate of an augmented diffusion is the deterministic
absolute clock, because its Brownian coefficient vanishes and drift is one. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (hbc : Continuous m.augmentedDrift)
    (B : ℝ) (hbB : ∀ z, ‖m.augmentedDrift z‖ ≤ B)
    (u : ℝ) (hu : 0 ≤ u) :
    (fun ω => m.augmentedPath u ω (1 : Fin 2)) =ᵐ[P]
      (fun _ => m.initialTime + u) := by
  let ℓ : (Fin 2 → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (1 : Fin 2)
  have hnoise : ∀ z (k : Fin 1), ℓ (m.augmentedVolatility z k) = 0 := by
    intro z k
    have hk : k = (0 : Fin 1) := Subsingleton.elim k 0
    subst k
    simpa [ℓ] using m.augmentedVolatility_clock z
  have hcore :=
    FunctionalInequalities.Probability.Diffusion.IsDiffusion.ae_linear_eq_integral_readable
      hbc hbB m.isDiffusion ℓ hnoise
  filter_upwards [hcore] with ω hω
  have hωu := hω u hu
  have hintegrand :
      (fun s => ℓ (m.augmentedDrift (m.augmentedPath s ω))) =
        (fun _ => (1 : ℝ)) := by
    funext s
    simp [ℓ, m.augmentedDrift_clock]
  rw [hintegrand] at hωu
  simpa [ℓ, m.initialCoordinates_clock, MeasureTheory.integral_const,
    Real.volume_real_Ioc_of_le hu] using hωu
