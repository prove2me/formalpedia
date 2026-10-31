-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_postPayment_frozen_stieltjes_tail_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:54:34.005003+00:00
-- url     : https://prove2.me/submissions/7ea44760-8706-4a31-a81a-699f3a4c4b86

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_truncated_global_variation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Freezing the true post-payment reserve at T kills all later
    Stieltjes mass of a Lipschitz test, with no truncation artefact. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (v : ℝ → ℝ) (L : NNReal) (hv : LipschitzWith L v) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      let g : ℝ≥0 → ℝ := fun t =>
        v (x + X.X (min t T) ω - rightLimit D (min t T) ω)
      ∃ hg : BoundedVariationOn g Set.univ,
        hg.vectorMeasure (Ioi T) = 0 := by
  filter_upwards [
    avram_wave3_03_bv_postPayment_truncated_global_variation X hX hBV x D hD
  ] with ω hω
  intro T
  let r : ℝ≥0 → ℝ := fun t =>
    x + X.X (min t T) ω - rightLimit D (min t T) ω
  let g : ℝ≥0 → ℝ := fun t => v (r t)
  change ∃ hg : BoundedVariationOn g Set.univ,
    hg.vectorMeasure (Ioi T) = 0
  have hr : BoundedVariationOn r Set.univ := hω T
  have hg : BoundedVariationOn g Set.univ :=
    hv.comp_boundedVariationOn hr
  have heq (t : ℝ≥0) (ht : T ≤ t) : g t = g T := by
    simp only [g, r, min_eq_right ht, min_self]
  have htop : Tendsto g atTop (𝓝 (g T)) := by
    have hevent : (fun _ : ℝ≥0 => g T) =ᶠ[atTop] g := by
      filter_upwards [eventually_ge_atTop T] with t ht
      exact (heq t ht).symm
    exact Tendsto.congr' hevent tendsto_const_nhds
  have hright : Tendsto g (𝓝[>] T) (𝓝 (g T)) := by
    have hevent : (fun _ : ℝ≥0 => g T) =ᶠ[𝓝[>] T] g := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (heq t (le_of_lt ht)).symm
    exact Tendsto.congr' hevent tendsto_const_nhds
  have hlim : limUnder atTop g = g T :=
    tendsto_nhds_unique hg.tendsto_atTop_limUnder htop
  have hrightlim : Function.rightLim g T = g T :=
    rightLim_eq_of_tendsto hright
  refine ⟨hg, ?_⟩
  rw [hg.vectorMeasure_Ioi T, hlim, hrightlim]
  exact sub_self _
