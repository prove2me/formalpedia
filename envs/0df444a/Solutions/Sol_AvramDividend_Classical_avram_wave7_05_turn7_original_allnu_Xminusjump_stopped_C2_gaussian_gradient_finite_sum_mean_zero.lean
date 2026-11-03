-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_finite_sum_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:14:26.769187+00:00
-- url     : https://prove2.me/submissions/991cb581-501d-414f-a018-7abe98ba301d

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

/-! Finite stopped source derivative Gaussian martingale gains are integrable and centred. -/
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
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ι → ℝ≥0)
    (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
    (h : ι → ℝ≥0) (G : ι → Ω → ℝ)
    (hGsource : ∀ i ∈ S, G i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0)))
    (BG : ι → ℝ) (hBG : ∀ i ∈ S, 0 ≤ BG i)
    (hGbound : ∀ i ∈ S, ∀ ω, |G i ω| ≤ BG i) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let V : ι → Ω → ℝ := fun i ω =>
      M (τ i ω + h i) ω - M (τ i ω) ω
    Integrable (fun ω => ∑ i ∈ S, G i ω * V i ω) P ∧
      (∫ ω, ∑ i ∈ S, G i ω * V i ω ∂P) = 0 := by
  classical
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
  let V : ι → Ω → ℝ := fun i ω =>
    M (τ i ω + h i) ω - M (τ i ω) ω
  let A : ι → Ω → ℝ := fun i ω => G i ω * V i ω
  have hEach : ∀ i ∈ S,
      Integrable (A i) P ∧ (∫ ω, A i ω ∂P) = 0 := by
    intro i hi
    have hOne :=
      avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_L2_isometry
        X Y hYν hYσ Jsmall Jlarge hSourceDecomp
        x D hD w C hw q T
        (τ i) (hτ i hi) (B i) (hbounded i hi)
        (h i) (G i) (hGsource i hi)
        (BG i) (hBG i hi) (hGbound i hi)
    dsimp only at hOne
    exact ⟨hOne.2.1, hOne.2.2.1⟩
  have hAll : ∀ i ∈ S, Integrable (A i) P :=
    fun i hi => (hEach i hi).1
  change Integrable (fun ω => ∑ i ∈ S, A i ω) P ∧
    (∫ ω, ∑ i ∈ S, A i ω ∂P) = 0
  refine ⟨integrable_finset_sum S hAll, ?_⟩
  calc
    (∫ ω, ∑ i ∈ S, A i ω ∂P) =
        ∑ i ∈ S, (∫ ω, A i ω ∂P) :=
      integral_finset_sum S hAll
    _ = 0 := by
      simp only [Finset.sum_eq_zero (fun i hi => (hEach i hi).2)]
