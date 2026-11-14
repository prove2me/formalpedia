-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_positive_cutoff_residual_retained_independence_20261113
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:31:12.356686+00:00
-- url     : https://prove2.me/submissions/3b906941-1590-4409-93fa-9dae0eea5ff3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_gaussian_core_and_jump_cutoff_measurable
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_disjoint_gaussian_retained_joint_charfun_factor_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical WithLp
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original source disjoint-noise independence follows from joint Fourier factorisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0), 0 < t →
      ProbabilityTheory.IndepFun
        (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X (n + 1) t ω)
        (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X (n + 1) t ω)
        P := by
  intro n t ht
  letI : IsProbabilityMeasure P := X.isProbability
  let R : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X (n + 1) t ω
  let J : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_small_band_compensated X (n + 1) t ω
  have hRm : Measurable R :=
    (avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X (n + 1) t).mono (𝓕.le t) le_rfl
  have hNegJ : Measurable (fun ω => -J ω) :=
    (avram_ja21_original_gaussian_core_and_jump_cutoff_measurable
      X (n + 1) t).2.mono (𝓕.le t) le_rfl
  have hJm : Measurable J := by
    have h := hNegJ.neg
    change Measurable (fun ω => -(-(J ω))) at h
    simpa only [neg_neg] using h
  have hChar :=
    avram_a21_original_disjoint_gaussian_retained_joint_charfun_factor_20261113
      X hX hFinite n t ht
  change ∀ u : WithLp 2 (ℝ × ℝ),
      charFun (P.map (fun ω => toLp 2 (R ω, J ω))) u =
        charFun (P.map R) u.ofLp.1 *
        charFun (P.map J) u.ofLp.2 at hChar
  exact (indepFun_iff_charFun_prod hRm.aemeasurable hJm.aemeasurable).2 hChar
