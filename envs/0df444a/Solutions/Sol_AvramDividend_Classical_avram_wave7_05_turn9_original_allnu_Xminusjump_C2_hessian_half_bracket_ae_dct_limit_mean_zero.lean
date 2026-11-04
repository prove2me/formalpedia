-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn9_original_allnu_Xminusjump_C2_hessian_half_bracket_ae_dct_limit_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:57:36.775506+00:00
-- url     : https://prove2.me/submissions/2ffe8946-bfee-45fb-8392-cec5717da911

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn8_original_allnu_Xminusjump_C2_hessian_finite_half_bracket_mean_zero
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Original C2 Hessian stopped Gaussian half bracket dominated limit. -/
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
    (Z g : Ω → ℝ) (hgI : Integrable g P) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let V : ℕ → ι → Ω → ℝ := fun n i ω =>
      M (τ n i ω + h n i) ω - M (τ n i ω) ω
    let Q : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ S n,
        ((1 / 2 : ℝ) * (((1 : ℝ) * V n i ω) *
          (H n i ω * V n i ω)) -
          (((h n i : ℝ) * X.σ ^ 2) / 2) * H n i ω)
    (∀ n, ∀ᵐ ω ∂P, ‖Q n ω‖ ≤ g ω) →
    (∀ᵐ ω ∂P, Tendsto (fun n => Q n ω) atTop (nhds (Z ω))) →
    (∫ ω, Z ω ∂P) = 0 := by
  classical
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
  let V : ℕ → ι → Ω → ℝ := fun n i ω =>
    M (τ n i ω + h n i) ω - M (τ n i ω) ω
  let Q : ℕ → Ω → ℝ := fun n ω =>
    ∑ i ∈ S n,
      ((1 / 2 : ℝ) * (((1 : ℝ) * V n i ω) *
        (H n i ω * V n i ω)) -
        (((h n i : ℝ) * X.σ ^ 2) / 2) * H n i ω)
  change (∀ n, ∀ᵐ ω ∂P, ‖Q n ω‖ ≤ g ω) →
    (∀ᵐ ω ∂P, Tendsto (fun n => Q n ω) atTop (nhds (Z ω))) →
    (∫ ω, Z ω ∂P) = 0
  intro hDom hConv
  have hEach : ∀ n : ℕ,
      Integrable (Q n) P ∧ (∫ ω, Q n ω ∂P) = 0 := by
    intro n
    have hOne :=
      avram_wave7_05_turn8_original_allnu_Xminusjump_C2_hessian_finite_half_bracket_mean_zero
        X Y hYν hYσ Jsmall Jlarge hSourceDecomp
        x D hD w C hw q T (S n) (τ n) (hτ n)
        (B n) (hbounded n) (h n) (H n) (hHsource n)
        (BH n) (hBH n) (hHbound n)
    dsimp only at hOne
    exact hOne
  have hMeas : ∀ n, AEStronglyMeasurable (Q n) P :=
    fun n => (hEach n).1.aestronglyMeasurable
  have hT := MeasureTheory.tendsto_integral_of_dominated_convergence
    g hMeas hgI hDom hConv
  have hZeroFun : (fun n : ℕ => ∫ ω, Q n ω ∂P) =
      (fun _ : ℕ => (0 : ℝ)) := by
    funext n
    exact (hEach n).2
  rw [hZeroFun] at hT
  have hConst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds (0 : ℝ)) :=
    tendsto_const_nhds
  exact (tendsto_nhds_unique hConst hT).symm
