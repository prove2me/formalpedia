-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_canonical_gaussian_martingale_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:12:32.776531+00:00
-- url     : https://prove2.me/submissions/299ffd36-0296-47d7-8ded-be0a32938ece

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_adapted_zero_origin_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original physical Gaussian martingale property transfers to a globally adapted canonical source. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (hMart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (R t) ω = R s ω) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω : Ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (G t) ω = G s ω) := by
  obtain ⟨G, hAdapt, hZero, hEq⟩ :=
    avram_a24_original_gaussian_adapted_zero_origin_20261113 X R hR
  refine ⟨G, hAdapt, hZero, hEq, ?_⟩
  intro s t hst
  have hGt : (G t) =ᵐ[P] (R t) := by
    filter_upwards [hEq] with ω hω
    exact hω t
  have hCE : condExp (𝓕.rightCont s) P (G t) =ᵐ[P]
      condExp (𝓕.rightCont s) P (R t) := condExp_congr_ae hGt
  filter_upwards [hCE, hMart s t hst, hEq] with ω hCEω hMω hGω
  calc
    condExp (𝓕.rightCont s) P (G t) ω =
      condExp (𝓕.rightCont s) P (R t) ω := hCEω
    _ = R s ω := hMω
    _ = G s ω := (hGω s).symm
