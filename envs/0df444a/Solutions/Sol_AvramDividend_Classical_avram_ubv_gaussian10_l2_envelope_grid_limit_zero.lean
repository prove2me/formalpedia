-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_l2_envelope_grid_limit_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:49:08.069201+00:00
-- url     : https://prove2.me/submissions/e6f40b90-4adc-4ac1-a94e-caa157a2fd32

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- A genuine L² envelope on the original Levy sample space transfers
finite-grid Gaussian zero means to the stopped limiting integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (G : ℕ → Ω → ℝ)
    (hGI : ∀ n, Integrable (G n) P)
    (hGzero : ∀ n, (∫ ω, G n ω ∂P) = 0)
    (D : Ω → ℝ) (hD : MemLp D 2 P)
    (hBound : ∀ n, ∀ᵐ ω ∂P, |G n ω| ≤ D ω)
    (M : Ω → ℝ)
    (hConv : ∀ᵐ ω ∂P, Tendsto (fun n => G n ω) atTop (𝓝 (M ω))) :
    Integrable M P ∧ (∫ ω, M ω ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hDI : Integrable D P :=
    hD.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hMm : AEStronglyMeasurable M P :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (hGI n).aestronglyMeasurable) hConv
  have hMb : ∀ᵐ ω ∂P, |M ω| ≤ D ω := by
    filter_upwards [hConv, ae_all_iff.mpr hBound] with ω hc hb
    exact le_of_tendsto hc.abs (Eventually.of_forall hb)
  have hMI : Integrable M P :=
    hDI.mono' hMm (hMb.mono fun ω hw => by
      simpa only [Real.norm_eq_abs] using hw)
  have ht := tendsto_integral_of_dominated_convergence
    D (fun n => (hGI n).aestronglyMeasurable) hDI
    (fun n => (hBound n).mono fun ω hw => by
      simpa only [Real.norm_eq_abs] using hw) hConv
  refine ⟨hMI, ?_⟩
  exact tendsto_nhds_unique ht (by
    simpa only [hGzero] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))