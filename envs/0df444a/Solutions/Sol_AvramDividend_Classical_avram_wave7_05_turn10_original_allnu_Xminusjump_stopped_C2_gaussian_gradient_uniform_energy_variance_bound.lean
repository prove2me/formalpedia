-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn10_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_uniform_energy_variance_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:55:48.626652+00:00
-- url     : https://prove2.me/submissions/66ce129a-8bd5-4170-9c3d-bc11f9ac2f3d

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_L2_isometry
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Source-specific Gaussian stopped derivative energy bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω + Jlarge t ω)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ n, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n ω ≤ s})
    (B : ℕ → ℝ≥0) (hbounded : ∀ n ω, τ n ω ≤ B n)
    (h : ℕ → ℝ≥0) (hStep : ∀ n, h n ≤ T)
    (G : ℕ → Ω → ℝ)
    (hGsource : ∀ n, G n = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n ω : WithTop ℝ≥0)))
    (BG : ℕ → ℝ) (hBG : ∀ n, 0 ≤ BG n)
    (hGbound : ∀ n ω, |G n ω| ≤ BG n)
    (E : ℝ) (hE : 0 ≤ E)
    (hEnergy : ∀ n, (∫ ω, G n ω * G n ω ∂P) ≤ E) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let V : ℕ → Ω → ℝ := fun n ω =>
      M (τ n ω + h n) ω - M (τ n ω) ω
    ∀ n, (∫ ω, (G n ω * V n ω) ^ 2 ∂P) ≤
      (T : ℝ) * X.σ ^ 2 * E := by
  classical
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
  let V : ℕ → Ω → ℝ := fun n ω =>
    M (τ n ω + h n) ω - M (τ n ω) ω
  change ∀ n, (∫ ω, (G n ω * V n ω) ^ 2 ∂P) ≤
    (T : ℝ) * X.σ ^ 2 * E
  intro n
  have hOne :=
    avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_L2_isometry
      X Y hYν hYσ Jsmall Jlarge hSourceDecomp x D hD w C hw
      q T (τ n) (hτ n) (B n) (hbounded n)
      (h n) (G n) (hGsource n)
      (BG n) (hBG n) (hGbound n)
  dsimp only at hOne
  have hVar : (∫ ω, (G n ω * V n ω) ^ 2 ∂P) =
      ((h n : ℝ) * X.σ ^ 2) * (∫ ω, G n ω * G n ω ∂P) :=
    hOne.2.2.2
  have hh : (h n : ℝ) ≤ (T : ℝ) := by exact_mod_cast hStep n
  have hh0 : (0 : ℝ) ≤ (h n : ℝ) := (h n).property
  have hσ : 0 ≤ X.σ ^ 2 := sq_nonneg _
  calc
    (∫ ω, (G n ω * V n ω) ^ 2 ∂P) =
        ((h n : ℝ) * X.σ ^ 2) * (∫ ω, G n ω * G n ω ∂P) := hVar
    _ ≤ ((h n : ℝ) * X.σ ^ 2) * E :=
      mul_le_mul_of_nonneg_left (hEnergy n) (mul_nonneg hh0 hσ)
    _ ≤ ((T : ℝ) * X.σ ^ 2) * E := by
      calc
        _ = (h n : ℝ) * (X.σ ^ 2 * E) := by ring
        _ ≤ (T : ℝ) * (X.σ ^ 2 * E) :=
          mul_le_mul_of_nonneg_right hh (mul_nonneg hσ hE)
        _ = _ := by ring
    _ = (T : ℝ) * X.σ ^ 2 * E := by ring
