-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn6_original_allnu_source_C2_gaussian_half_bracket_L1_localisation_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:37:19.164033+00:00
-- url     : https://prove2.me/submissions/140d341d-59a1-4938-bfd5-84d208c6c9fb

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn6_original_allnu_source_C2_gaussian_finite_half_bracket_compensation_mean_zero
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Original-source Gaussian C2 half-bracket localisation: every bounded
compensated quadratic mesh is centred, and an L1 limit remains centred. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
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
    (S : ℕ → Finset ι) (τ : ℕ → ι → Ω → ℝ≥0)
    (hτ : ∀ n, ∀ i ∈ S n, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n i ω ≤ s})
    (B : ℕ → ι → ℝ≥0)
    (hbounded : ∀ n, ∀ i ∈ S n, ∀ ω, τ n i ω ≤ B n i)
    (h : ℕ → ι → ℝ≥0) (H : ℕ → ι → Ω → ℝ)
    (hHsource : ∀ n, ∀ i ∈ S n, H n i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n i ω : WithTop ℝ≥0)))
    (BH : ℕ → ι → ℝ)
    (hBH : ∀ n, ∀ i ∈ S n, 0 ≤ BH n i)
    (hHbound : ∀ n, ∀ i ∈ S n, ∀ ω, |H n i ω| ≤ BH n i)
    (M : Ω → ℝ) (hMI : Integrable M P) :
    let V : ℕ → ι → Ω → ℝ := fun n i ω =>
      Y.X (τ n i ω + h n i) ω - Y.X (τ n i ω) ω -
        (h n i : ℝ) * Y.c
    let Q : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ S n,
        ((1 / 2 : ℝ) * (((1 : ℝ) * V n i ω) *
          (H n i ω * V n i ω)) -
        (((h n i : ℝ) * X.σ ^ 2) / 2) * H n i ω)
    Tendsto (fun n => ∫⁻ ω, ‖Q n ω - M ω‖ₑ ∂P) atTop (nhds 0) →
      (∫ ω, M ω ∂P) = 0 := by
  classical
  let V : ℕ → ι → Ω → ℝ := fun n i ω =>
    Y.X (τ n i ω + h n i) ω - Y.X (τ n i ω) ω -
      (h n i : ℝ) * Y.c
  let Q : ℕ → Ω → ℝ := fun n ω =>
    ∑ i ∈ S n,
      ((1 / 2 : ℝ) * (((1 : ℝ) * V n i ω) *
        (H n i ω * V n i ω)) -
      (((h n i : ℝ) * X.σ ^ 2) / 2) * H n i ω)
  dsimp only
  intro hL1
  have hEach : ∀ n : ℕ,
      Integrable (Q n) P ∧ (∫ ω, Q n ω ∂P) = 0 := by
    intro n
    have hOne :=
      avram_wave7_05_turn6_original_allnu_source_C2_gaussian_finite_half_bracket_compensation_mean_zero
        X Y hYν hYσ Jsmall Jlarge hSourceDecomp
        x D hD w C hw q T
        (S n) (τ n) (hτ n) (B n) (hbounded n)
        (h n) (H n) (hHsource n) (BH n)
        (hBH n) (hHbound n)
    dsimp only at hOne
    exact hOne
  have hIntegrable : ∀ n : ℕ, Integrable (Q n) P :=
    fun n => (hEach n).1
  have hT :=
    tendsto_integral_of_L1 M hMI.aestronglyMeasurable
      (Filter.Eventually.of_forall hIntegrable) hL1
  have hZeroFun : (fun n : ℕ => ∫ ω, Q n ω ∂P) =
      (fun _ : ℕ => (0 : ℝ)) := by
    funext n
    exact (hEach n).2
  rw [hZeroFun] at hT
  have hConst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds (0 : ℝ)) :=
    tendsto_const_nhds
  exact (tendsto_nhds_unique hConst hT).symm
