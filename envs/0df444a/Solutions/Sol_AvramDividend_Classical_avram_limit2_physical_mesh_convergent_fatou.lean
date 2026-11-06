-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_physical_mesh_convergent_fatou
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:16:42.438884+00:00
-- url     : https://prove2.me/submissions/8840fac0-8041-4b5b-8e8c-3ae95b996718

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Almost-everywhere convergence of a physical real stopped mesh gives the
    exact nonnegative extended-real Fatou lower bound used in verification. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ) (R : Ω → ℝ)
    (hR : ∀ᵐ ω ∂P,
      Tendsto (fun n => F n ω) atTop (nhds (R ω))) :
    ∀ᵐ ω ∂P,
      ENNReal.ofReal (R ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop := by
  filter_upwards [hR] with ω hω
  have hE : Tendsto (fun n => ENNReal.ofReal (F n ω)) atTop
      (nhds (ENNReal.ofReal (R ω))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hω
  rw [hE.liminf_eq]
