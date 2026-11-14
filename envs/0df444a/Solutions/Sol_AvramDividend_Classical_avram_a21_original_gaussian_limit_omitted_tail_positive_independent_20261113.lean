-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_gaussian_limit_omitted_tail_positive_independent_20261113
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:24:56.263209+00:00
-- url     : https://prove2.me/submissions/53e8bda1-8afa-4219-b6f5-151d7d8b52ff
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_intrinsic_limit_ae_adapted_of_cutoff_convergence
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_omitted_tail_joint_charfun_factor_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical WithLp
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original Gaussian limit versus omitted jump tail independence from joint Fourier factorisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    ∀ (n : ℕ) (t : ℝ≥0), 0 < t →
      ProbabilityTheory.IndepFun
        (R t)
        (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω)
        P := by
  intro n t ht
  letI : IsProbabilityMeasure P := X.isProbability
  let J : Ω → ℝ := fun ω =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω
  have hCut (k : ℕ) (T : ℝ≥0) :
      Measurable[𝓕.rightCont T]
        (fun ω : Ω => avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω) :=
    (avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X k T).mono (𝓕.le_rightCont T) le_rfl
  have hRmeas : AEStronglyMeasurable (R t) P :=
    (avram_mix_inf15_original_intrinsic_limit_ae_adapted_of_cutoff_convergence
      X hCut R hR t).mono ((𝓕.rightCont).le t)
  have hCutMeas : AEStronglyMeasurable
      (fun ω : Ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) P :=
    ((avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X n t).mono (𝓕.le t) le_rfl).aestronglyMeasurable
  have hJmeas : AEStronglyMeasurable J P :=
    hCutMeas.sub hRmeas
  have hChar :=
    avram_a21_original_gaussian_limit_omitted_tail_joint_charfun_factor_20261113
      X hX hFinite R hR n t ht
  change ∀ u : WithLp 2 (ℝ × ℝ),
      charFun (P.map (fun ω => toLp 2 (R t ω, J ω))) u =
        charFun (P.map (R t)) u.ofLp.1 *
        charFun (P.map J) u.ofLp.2 at hChar
  exact (indepFun_iff_charFun_prod
    hRmeas.aemeasurable hJmeas.aemeasurable).2 hChar
