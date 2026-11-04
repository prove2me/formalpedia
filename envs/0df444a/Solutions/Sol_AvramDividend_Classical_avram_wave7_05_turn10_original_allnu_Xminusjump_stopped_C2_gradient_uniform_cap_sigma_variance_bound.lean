-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn10_original_allnu_Xminusjump_stopped_C2_gradient_uniform_cap_sigma_variance_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:07:11.067693+00:00
-- url     : https://prove2.me/submissions/252ba3ae-9b39-4ede-8daf-11382d9d7730

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn10_original_stopped_C2_predictable_gradient_uniform_bound_integral_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn10_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_uniform_energy_variance_bound
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Original controlled C2 stopped Gaussian variance from a deterministic gradient cap. -/
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
    (K : ℝ) (hK : 0 ≤ K)
    (hGbound : ∀ n ω, |G n ω| ≤ K) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let V : ℕ → Ω → ℝ := fun n ω =>
      M (τ n ω + h n) ω - M (τ n ω) ω
    ∀ n, (∫ ω, (G n ω * V n ω) ^ 2 ∂P) ≤
      (T : ℝ) * X.σ ^ 2 * K ^ 2 := by
  classical
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
  let V : ℕ → Ω → ℝ := fun n ω =>
    M (τ n ω + h n) ω - M (τ n ω) ω
  have hEnergy :=
    avram_wave7_05_turn10_original_stopped_C2_predictable_gradient_uniform_bound_integral_energy
      X x D hD w C hw q T τ hτ G hGsource K hK hGbound
  have hVar :=
    avram_wave7_05_turn10_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_uniform_energy_variance_bound
      X Y hYν hYσ Jsmall Jlarge hSourceDecomp
      x D hD w C hw q T τ hτ B hbounded h hStep
      G hGsource (fun _ => K) (fun _ => hK) hGbound
      (K ^ 2) (sq_nonneg K) (fun n => (hEnergy n).2)
  dsimp only at hVar
  change ∀ n, (∫ ω, (G n ω * V n ω) ^ 2 ∂P) ≤
      (T : ℝ) * X.σ ^ 2 * K ^ 2
  simpa only [mul_assoc] using hVar
