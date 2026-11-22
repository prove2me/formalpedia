-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_zerojump_canonical_ruinclip_gaussian_square_and_compensator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:22:25.0768+00:00
-- url     : https://prove2.me/submissions/35332e59-69b8-4fe8-9dff-5814e53f98b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_zerojump_arbitrary_bounded_stop_exact_energy

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/- Actual original zero-jump spectrally negative Levy process, actual
   dividend strategy and ruin-clipped stopping time. Derives both stopped
   Gaussian quadratic isometry and integrable mean-zero compensated-square
   residual. Adapted from dufeteller/lean-lsv LocalizedStoppingL2Convergence
   and LocalizedOptionalExpectation, CC BY 4.0 commit a5f604d. -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω,
      τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    let M : Ω → ℝ := fun ω =>
      X.X (τ ω) ω - (τ ω : ℝ) * X.c
    Integrable (fun ω => (M ω)^2) P ∧
      (∫ ω, (M ω)^2 ∂P) =
        ∫ ω, (τ ω : ℝ) * X.σ^2 ∂P ∧
    Integrable (fun ω => (M ω)^2 - (τ ω : ℝ) * X.σ^2) P ∧
      (∫ ω, (M ω)^2 - (τ ω : ℝ) * X.σ^2 ∂P) = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0) := by
    intro ω
    rw [hτeq ω]
    have hmin :
        (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ≤
          ((n : ℝ≥0) : ℝ≥0∞).toNNReal :=
      ENNReal.toNNReal_mono (by simp) (min_le_right _ _)
    simpa only [ENNReal.toNNReal_coe] using hmin
  have hMoment :=
    avram_lsv_original_zerojump_arbitrary_bounded_stop_exact_energy
      X hν n hn τ hτstop hτbound hτmeas
  have hτI : Integrable (fun ω => (τ ω : ℝ)) P := by
    apply (integrable_const (n : ℝ)).mono'
      hτmeas.aestronglyMeasurable
    exact ae_of_all _ (fun ω => by
      have hle : (τ ω : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hτbound ω
      simpa [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] using hle)
  have hVI : Integrable (fun ω => (τ ω : ℝ) * X.σ^2) P :=
    hτI.mul_const _
  change Integrable (fun ω =>
      (X.X (τ ω) ω - (τ ω : ℝ) * X.c)^2) P ∧
    (∫ ω, (X.X (τ ω) ω - (τ ω : ℝ) * X.c)^2 ∂P) =
      ∫ ω, (τ ω : ℝ) * X.σ^2 ∂P ∧
    Integrable (fun ω => (X.X (τ ω) ω -
      (τ ω : ℝ) * X.c)^2 - (τ ω : ℝ) * X.σ^2) P ∧
    (∫ ω, (X.X (τ ω) ω -
      (τ ω : ℝ) * X.c)^2 - (τ ω : ℝ) * X.σ^2 ∂P) = 0
  refine ⟨hMoment.1, hMoment.2, hMoment.1.sub hVI, ?_⟩
  rw [integral_sub hMoment.1 hVI, hMoment.2, sub_self]

