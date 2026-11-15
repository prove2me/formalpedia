-- Prove2me | solution 1 for AvramDividend.Classical.avram_b79_original_true_stop_source_energy_gaussian_only
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:08:43.111786+00:00
-- url     : https://prove2.me/submissions/ad3c31dc-58f2-42b2-86d8-aa2f249b8810

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_b73_original_actual_ruinclipped_strict_interior_mixed_energy
import Theorems.Thm_AvramDividend_Classical_avram_b74_original_true_stopping_grid_mixed_source_duration_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b78_original_jumpfree_interior_cell_gaussian_residual_drift_decomp
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Actual original clipped interior stopped source energy from the intrinsic Gaussian and negative mark decomposition. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω)))
    (x : ℝ) (hx : 0 < x) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hρclip : ∀ ω, ρ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (κ : ℕ → Ω → ℝ≥0)
    (hκexact : ∀ k ω, κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal)
    (k : ℕ) (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (J : Ω → Finset ℕ)
    (d : ℝ)
    (hInterior : ∀ ω i, i ∈ S →
      s i ω ≤ t i ω ∧
      (t i ω : ℝ≥0∞) < (κ k ω : ℝ≥0∞))
    (hJsub : ∀ ω, J ω ⊆ S)
    (hJmeas : Measurable (fun ω : Ω => ((J ω).card : ℝ)))
    (hJdom : ∀ ω : Ω, ((J ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ))).toReal)
    (hsStop : ∀ i ∈ S, IsStoppingTime 𝓕.rightCont
      (fun ω => (s i ω : WithTop ℝ≥0)))
    (htStop : ∀ i ∈ S, IsStoppingTime 𝓕.rightCont
      (fun ω => (t i ω : WithTop ℝ≥0)))
    (hSmall : ∀ ω i, i ∈ S → i ∉ J ω →
      Jsmall (t i ω) ω - Jsmall (s i ω) ω =
        d * (((t i ω - s i ω : ℝ≥0) : ℝ)))
    (hLarge : ∀ ω i, i ∈ S → i ∉ J ω →
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (t i ω) ω =
      avram_p4_h_gaussian_intrinsic_large_jump_sum X (s i ω) ω) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0, M u ω = R u ω) ∧
      let E : Ω → ℝ := fun ω =>
        ∑ i ∈ S, (X.X (t i ω) ω - X.X (s i ω) ω -
          ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2
      let G : Ω → ℝ := fun ω =>
        ∑ i ∈ S, (M (t i ω) ω - M (s i ω) ω)^2
      let Dur : Ω → ℝ := fun ω =>
        ∑ i ∈ S, (((t i ω - s i ω : ℝ≥0) : ℝ))^2
      Integrable G P →
      Integrable E P ∧ (∫ ω, E ω ∂P) ≤
        2 * (∫ ω, G ω ∂P) +
        2 * d^2 * (∫ ω, Dur ω ∂P) +
        (x + ((k : ℝ) + 1) + ((n : ℝ≥0) : ℝ) * |X.c|)^2 *
        (((n : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := by
  have hOrdered (ω : Ω) (i : ℕ) (hi : i ∈ S) :
      s i ω ≤ t i ω := (hInterior ω i hi).1
  obtain ⟨M, hMsource, hNoJump⟩ :=
    avram_b78_original_jumpfree_interior_cell_gaussian_residual_drift_decomp
      X R Jsmall hRsource hJsource S s t J d
      hOrdered hSmall hLarge
  refine ⟨M, hMsource, ?_⟩
  intro E G Dur hGI
  have hMeas :=
    avram_b74_original_true_stopping_grid_mixed_source_duration_measurable
      X S s t hsStop htStop hOrdered
  have hDurMeas : AEStronglyMeasurable (fun ω : Ω =>
      ∑ i ∈ S, (((t i ω - s i ω : ℝ≥0) : ℝ))^2) P :=
    hMeas.2.aestronglyMeasurable
  exact avram_b73_original_actual_ruinclipped_strict_interior_mixed_energy
    X hFinite x hx C D hD n ρ hρbound hρclip κ hκexact
    k S s t (fun i ω => M (t i ω) ω - M (s i ω) ω)
    J d hInterior hJsub hJmeas hJdom
    hNoJump hMeas.1 hGI hDurMeas
