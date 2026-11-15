-- Prove2me | solution 1 for AvramDividend.Classical.avram_a42_original_gaussian_alltime_ae_representative_inherits_martingale_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:23:02.07324+00:00
-- url     : https://prove2.me/submissions/6e5e5e56-4364-4c25-a317-4483626c7c1b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R G : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (hEq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) :
    (∀ t : ℝ≥0, Integrable (G t) P) ∧
    (∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (G t) ω = G s ω) := by
  obtain ⟨H, hHlim, _, hHInt, hHCond⟩ :=
    avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
      X hX hFinite
  have hHR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, H t ω = R t ω := by
    filter_upwards [hHlim, hR] with ω hHω hRω
    intro t
    exact tendsto_nhds_unique (hHω.1 t) (hRω t)
  have hGH : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = H t ω := by
    filter_upwards [hHR, hEq] with ω hHω hGω
    intro t
    exact (hGω t).trans (hHω t).symm
  have hTime (t : ℝ≥0) : (G t) =ᵐ[P] (H t) := by
    filter_upwards [hGH] with ω hω
    exact hω t
  constructor
  · intro t
    exact (hHInt t).congr (hTime t).symm
  · intro s t hst
    have hCond :
        condExp (𝓕.rightCont s) P (G t) =ᵐ[P]
          condExp (𝓕.rightCont s) P (H t) :=
      condExp_congr_ae (hTime t)
    filter_upwards [hCond, hHCond s t hst, hTime s] with ω hω hMω hSω
    calc
      condExp (𝓕.rightCont s) P (G t) ω =
        condExp (𝓕.rightCont s) P (H t) ω := hω
      _ = H s ω := hMω
      _ = G s ω := hSω.symm
