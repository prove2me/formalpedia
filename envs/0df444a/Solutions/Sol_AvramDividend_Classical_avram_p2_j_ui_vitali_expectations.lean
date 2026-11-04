-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_vitali_expectations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:19:04.723103+00:00
-- url     : https://prove2.me/submissions/fc520337-9004-40f1-ad54-7c2fc5c40534

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter

/-! Vitali convergence for real-valued Bochner expectations. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hUI : UniformIntegrable Y 1 P)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by
  have hZ : Integrable Z P := hUI.integrable_of_ae_tendsto hae
  have hZLp : MemLp Z 1 P := memLp_one_iff_integrable.mpr hZ
  have hmeas : ∀ n, AEStronglyMeasurable (Y n) P :=
    fun n => hUI.aestronglyMeasurable n
  have hLp : Tendsto (fun n => eLpNorm (Y n - Z) 1 P) atTop (nhds 0) :=
    tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
      hmeas hZLp hUI.unifIntegrable hae
  have hY : ∀ n, Integrable (Y n) P :=
    fun n => memLp_one_iff_integrable.mp (hUI.memLp n)
  exact ⟨hZ, tendsto_integral_of_L1' Z hZ.aestronglyMeasurable
    (Filter.Eventually.of_forall hY) hLp⟩
