-- Prove2me | solution 1 for FeynmanKac.path_start_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:02:58.826326+00:00
-- url     : https://prove2.me/submissions/35c75411-4b2d-4bb8-b5f9-de4c9f40b69b

import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Theorems.Thm_FeynmanKac_diffusion_initial_ae
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- The real spatial path starts at the model's deterministic position,
by projecting the generic initial-value theorem for IsDiffusion. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P) :
    (fun ω => m.path m.initialTime ω) =ᵐ[P]
      (fun _ => m.initialState) := by
  filter_upwards [FeynmanKac.diffusion_initial_ae m.isDiffusion] with ω hω
  have hcoord := congrArg (fun z : Fin 2 → ℝ => z (0 : Fin 2)) hω
  simpa [FeynmanKac.BoundedDiffusionModel.path,
    m.initialCoordinates_space] using hcoord
