-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_mixed_canonical_ruinclip_gaussian_exact_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:51:43.181197+00:00
-- url     : https://prove2.me/submissions/007c6d85-eb92-4284-b4be-3942472a4b2c

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
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    Integrable (fun ω => (M (τ ω) ω)^2) P ∧
      (∫ ω, (M (τ ω) ω)^2 ∂P) =
        ∫ ω, (τ ω : ℝ) * X.σ^2 ∂P := by
  classical
  have hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0) := by
    intro ω
    rw [hτeq ω]
    have hmin :
        (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ≤
          ((n : ℝ≥0) : ℝ≥0∞).toNNReal :=
      ENNReal.toNNReal_mono (by simp) (min_le_right _ _)
    simpa only [ENNReal.toNNReal_coe] using hmin
  exact avram_lsv_original_allnu_arbitrary_bounded_stop_exact_energy
    X Y hYν hYσ Jsmall Jlarge hSourceDecomp
    n hn τ hτstop hτbound hτmeas

