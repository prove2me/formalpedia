-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn11_original_allnu_stopped_C2_gradient_cell_sigma_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:42:39.769227+00:00
-- url     : https://prove2.me/submissions/7e36e275-7794-465c-9fbe-37c8bbf6b99e

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_L2_isometry
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn10_original_stopped_C2_predictable_gradient_uniform_bound_integral_energy
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Actual source Gaussian stopped-gradient L² energy bound at a single clock. -/
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
    (τ : Ω → ℝ≥0)
    (hτ : ∀ u : ℝ≥0,
      MeasurableSet[𝓕.rightCont u] {ω : Ω | τ ω ≤ u})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (G : Ω → ℝ)
    (hGsource : G = stoppedValue (fun u ω =>
      if u ≤ T then
        (Real.exp (-(q * (u : ℝ))) *
          deriv w (Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u)) *
        (if (u : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0)))
    (K : ℝ) (hK : 0 ≤ K)
    (hGbound : ∀ ω, |G ω| ≤ K) :
    let M : ℝ≥0 → Ω → ℝ := fun u ω =>
      X.X u ω - (u : ℝ) * X.c - Jsmall u ω - Jlarge u ω
    let V : Ω → ℝ := fun ω => M (τ ω + h) ω - M (τ ω) ω
    MemLp (fun ω => G ω * V ω) 2 P ∧
      (∫ ω, (G ω * V ω) ^ 2 ∂P) ≤
        (h : ℝ) * X.σ ^ 2 * K ^ 2 := by
  classical
  let M : ℝ≥0 → Ω → ℝ := fun u ω =>
    X.X u ω - (u : ℝ) * X.c - Jsmall u ω - Jlarge u ω
  let V : Ω → ℝ := fun ω => M (τ ω + h) ω - M (τ ω) ω
  let τs : ℕ → Ω → ℝ≥0 := fun _ => τ
  let Gs : ℕ → Ω → ℝ := fun _ => G
  have hEnergy :=
    avram_wave7_05_turn10_original_stopped_C2_predictable_gradient_uniform_bound_integral_energy
      X x D hD w C hw q T τs (fun _ => hτ) Gs
      (fun _ => hGsource) K hK (fun _ => hGbound)
  have hE : (∫ ω, G ω * G ω ∂P) ≤ K ^ 2 :=
    (hEnergy 0).2
  have hOne :=
    avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_L2_isometry
      X Y hYν hYσ Jsmall Jlarge hSourceDecomp
      x D hD w C hw q T τ hτ B hbounded h G hGsource K hK hGbound
  dsimp only at hOne
  change MemLp (fun ω => G ω * V ω) 2 P ∧
      (∫ ω, (G ω * V ω) ^ 2 ∂P) ≤
        (h : ℝ) * X.σ ^ 2 * K ^ 2
  refine ⟨hOne.1, ?_⟩
  have hh0 : (0 : ℝ) ≤ (h : ℝ) := h.property
  have hσ : 0 ≤ X.σ ^ 2 := sq_nonneg _
  calc
    (∫ ω, (G ω * V ω) ^ 2 ∂P) =
        ((h : ℝ) * X.σ ^ 2) * (∫ ω, G ω * G ω ∂P) := hOne.2.2.2
    _ ≤ ((h : ℝ) * X.σ ^ 2) * K ^ 2 :=
      mul_le_mul_of_nonneg_left hE (mul_nonneg hh0 hσ)
    _ = (h : ℝ) * X.σ ^ 2 * K ^ 2 := by ring
