-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_gaussian_limit_raw_filtration_indep_of_ae_rep_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:39:22.628207+00:00
-- url     : https://prove2.me/submissions/634ce6b9-e270-4945-81a3-77b13e2bf6e5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a24_uniform_gaussian_limit_original_past_independent_rep_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a27_indep_source_sigma_comap_ae_congr_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Any all-time source-a.e. representative of the original Gaussian limit has original raw-filtration independent increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R G : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n u ω)
        atTop (𝓝 (R u ω)))
    (hEq : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, G u ω = R u ω) :
    ∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => G t ω - G s ω) inferInstance)
        (𝓕 s) P := by
  intro s t hst
  obtain ⟨D, _, hInd, hDEq⟩ :=
    avram_a24_uniform_gaussian_limit_original_past_independent_rep_20261113
      X hX hFinite R hR (t - s)
  have hAE : (D s) =ᵐ[P] (fun ω => G t ω - G s ω) := by
    filter_upwards [hDEq, hEq] with ω hDω hGω
    calc
      D s ω = R (s + (t - s)) ω - R s ω := hDω s
      _ = R t ω - R s ω := by rw [add_tsub_cancel_of_le hst]
      _ = G t ω - G s ω := by rw [← hGω t, ← hGω s]
  have hStrong :=
    avram_a27_indep_source_sigma_comap_ae_congr_20261114
      P (𝓕.rightCont s) (D s) (fun ω => G t ω - G s ω)
      (hInd s) hAE
  exact indep_of_indep_of_le_right hStrong (𝓕.le_rightCont s)
