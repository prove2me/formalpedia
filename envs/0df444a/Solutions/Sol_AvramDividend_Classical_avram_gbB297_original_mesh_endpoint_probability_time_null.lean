-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB297_original_mesh_endpoint_probability_time_null
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:20:03.07944+00:00
-- url     : https://prove2.me/submissions/ab8f04b0-8efe-4a94-864f-150e1b8ecc35

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB283_finite_physical_time_mesh_endpoints_null_volume
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite mesh boundaries have zero original probability-time product mass. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (N : ℕ) (δ : ℝ) :
    (P.prod volume)
      {z : Ω × ℝ |
        z.2 ∈ Set.range (fun i : Fin N => (i : ℝ) * δ)} = 0 := by
  let E : Set ℝ := Set.range (fun i : Fin N => (i : ℝ) * δ)
  have hE : MeasurableSet E := (Set.finite_range _).measurableSet
  have hS : MeasurableSet {z : Ω × ℝ | z.2 ∈ E} :=
    hE.preimage measurable_snd
  have hFiber (ω : Ω) :
      (Prod.mk ω ⁻¹' {z : Ω × ℝ | z.2 ∈ E}) = E := by
    ext t
    rfl
  change (P.prod volume) {z : Ω × ℝ | z.2 ∈ E} = 0
  rw [Measure.prod_apply hS]
  simp_rw [hFiber]
  have hnull : volume E = 0 :=
    avram_gbB283_finite_physical_time_mesh_endpoints_null_volume N δ
  simp [hnull]
