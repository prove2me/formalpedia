-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_zero_cutoff_conditional_increment_centred
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T03:53:14.043116+00:00
-- url     : https://prove2.me/submissions/60ca93fc-7628-4a96-8b20-ad235f41940e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_zero_cutoff_increment_rightcont_indep
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_zero_cutoff_increment_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original-filtration zero-cutoff Gaussian-core martingale, separated into
physical future independence and the original Levy-Khintchine mean identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hInt : ∀ t : ℝ≥0, Integrable
      (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) P) :
    ∀ s t : ℝ≥0, s ≤ t → ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont s) P
        (fun ω => avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) ω =
      avram_p4_h_gaussian_intrinsic_truncated_residual X 0 s ω := by
  letI : IsProbabilityMeasure P := X.isProbability
  let R0 (t : ℝ≥0) (ω : Ω) :=
    avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω
  intro s t hst
  let D : Ω → ℝ := fun ω => R0 t ω - R0 s ω
  have hRsInt : Integrable (R0 s) P := hInt s
  have hRtInt : Integrable (R0 t) P := hInt t
  have hDInt : Integrable D P := hRtInt.sub hRsInt
  have hFacts :=
    avram_ja18g_original_zero_cutoff_increment_rightcont_indep X hX hFinite s t hst
  obtain ⟨hDLe, hDStrong, hDIndep⟩ := hFacts
  have hMean : (∫ ω, D ω ∂P) = 0 := by
    simpa only [D, R0] using
      (avram_ja18g_original_zero_cutoff_increment_mean_zero X hX hFinite s t hst)
  have hCE : P[D | 𝓕.rightCont s] =ᵐ[P] fun _ => (0 : ℝ) := by
    have hIndepCE : P[D | 𝓕.rightCont s] =ᵐ[P]
        fun _ => ∫ ω, D ω ∂P :=
      condExp_indep_eq hDLe (𝓕.rightCont.le s) hDStrong hDIndep
    simpa only [hMean] using hIndepCE
  have hRsMeas : StronglyMeasurable[𝓕.rightCont s] (R0 s) := by
    exact ((avram_mix_gauss14_original_intrinsic_truncated_residual_adapted
      X 0 s).mono (𝓕.le_rightCont s) le_rfl).stronglyMeasurable
  have hSelf : P[R0 s | 𝓕.rightCont s] = R0 s :=
    condExp_of_stronglyMeasurable (𝓕.rightCont.le s) hRsMeas hRsInt
  have hEq : R0 t = R0 s + D := by
    funext ω
    dsimp [D, R0]
    ring
  change P[R0 t | 𝓕.rightCont s] =ᵐ[P] R0 s
  calc
    P[R0 t | 𝓕.rightCont s] =ᵐ[P]
        P[R0 s + D | 𝓕.rightCont s] := by rw [hEq]
    _ =ᵐ[P] P[R0 s | 𝓕.rightCont s] +
        P[D | 𝓕.rightCont s] :=
      condExp_add hRsInt hDInt (𝓕.rightCont s)
    _ =ᵐ[P] R0 s := by
      filter_upwards [hCE] with ω hω
      simp [hSelf, hω]
