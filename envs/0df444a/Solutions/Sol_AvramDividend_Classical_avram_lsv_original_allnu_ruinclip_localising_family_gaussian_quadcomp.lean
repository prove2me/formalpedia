-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_allnu_ruinclip_localising_family_gaussian_quadcomp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:37:40.490473+00:00
-- url     : https://prove2.me/submissions/7eb2183c-2c67-4b35-9649-4f4aaec54898

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_allnu_arbitrary_bounded_stop_exact_energy

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/- The exact original clipped ruin stop used by Avram, with its actual
   right-continuous stopping-time witness and the physical jump channels.
   Applies the remotely Proved genuine mixed Gaussian arbitrary-stop theorem
   derived from dufeteller/lean-lsv (CC BY 4.0, commit a5f604d). -/

/- The true original sigma_k family below the exact ruin-clipped tau.
   The original mixed Levy physical Gaussian and jump channels are retained.
   Adapted from dufeteller/lean-lsv CC BY 4.0 commit a5f604d. -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω + Jlarge t ω)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω,
      τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k, let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    Integrable (fun ω => (M (σ k ω) ω)^2) P ∧
      (∫ ω, (M (σ k ω) ω)^2 ∂P) =
        ∫ ω, (σ k ω : ℝ) * X.σ^2 ∂P ∧
      Integrable (fun ω =>
        (M (σ k ω) ω)^2 - (σ k ω : ℝ) * X.σ^2) P ∧
      (∫ ω, (M (σ k ω) ω)^2 -
        (σ k ω : ℝ) * X.σ^2 ∂P) = 0 := by
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
  intro k
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
  have hκbound : ∀ ω, σ k ω ≤ (n : ℝ≥0) := by
    intro ω
    exact (hσle k ω).trans (hτbound ω)
  have hσmeas : Measurable (fun ω => (σ k ω : ℝ)) := by
    exact measurable_coe_nnreal_real_iff.mpr
      (measurable_coe_nnreal_ennreal_iff.mp (hσstop k).measurable')
  have hEnergy :=
    avram_lsv_original_allnu_arbitrary_bounded_stop_exact_energy
      X Y hYν hYσ Jsmall Jlarge hSourceDecomp
      n hn (σ k) (hσstop k) hκbound hσmeas
  have hκI : Integrable (fun ω => (σ k ω : ℝ)) P := by
    apply (integrable_const (n : ℝ)).mono'
      hσmeas.aestronglyMeasurable
    exact ae_of_all _ (fun ω => by
      have hle : (σ k ω : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hκbound ω
      simpa [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] using hle)
  have hVI : Integrable (fun ω => (σ k ω : ℝ) * X.σ^2) P :=
    hκI.mul_const _
  change Integrable (fun ω => (M (σ k ω) ω)^2) P ∧
    (∫ ω, (M (σ k ω) ω)^2 ∂P) =
      ∫ ω, (σ k ω : ℝ) * X.σ^2 ∂P ∧
    Integrable (fun ω => (M (σ k ω) ω)^2 -
      (σ k ω : ℝ) * X.σ^2) P ∧
    (∫ ω, (M (σ k ω) ω)^2 -
      (σ k ω : ℝ) * X.σ^2 ∂P) = 0
  refine ⟨hEnergy.1, hEnergy.2, hEnergy.1.sub hVI, ?_⟩
  rw [integral_sub hEnergy.1 hVI, hEnergy.2, sub_self]

