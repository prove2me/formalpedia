-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn6_original_allnu_gaussian_gradient_L1_localisation_auto_predictable_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:24:24.25959+00:00
-- url     : https://prove2.me/submissions/0ae2883d-e2b4-467e-a36f-66762b7f000f

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn6_original_allnu_source_gaussian_multistop_gradient_automatic_L2_mean_zero
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Bounded original-source Gaussian stopped C2 gradient meshes are automatically
predictable and centred. Any integrable L1 limit is centred on original Ω/P. -/
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
    (h : ℕ → ι → ℝ≥0) (G : ℕ → ι → Ω → ℝ)
    (hGsource : ∀ n, ∀ i ∈ S n, G n i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n i ω : WithTop ℝ≥0)))
    (K : ℕ → ι → ℝ)
    (hK : ∀ n, ∀ i ∈ S n, 0 ≤ K n i)
    (hGbound : ∀ n, ∀ i ∈ S n, ∀ ω, |G n i ω| ≤ K n i)
    (M : Ω → ℝ) (hMI : Integrable M P) :
    let V : ℕ → ι → Ω → ℝ := fun n i ω =>
      Y.X (τ n i ω + h n i) ω - Y.X (τ n i ω) ω -
        (h n i : ℝ) * Y.c
    let F : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ S n, G n i ω * V n i ω
    Tendsto (fun n => ∫⁻ ω, ‖F n ω - M ω‖ₑ ∂P) atTop (nhds 0) →
      (∫ ω, M ω ∂P) = 0 := by
  classical
  let V : ℕ → ι → Ω → ℝ := fun n i ω =>
    Y.X (τ n i ω + h n i) ω - Y.X (τ n i ω) ω -
      (h n i : ℝ) * Y.c
  let F : ℕ → Ω → ℝ := fun n ω =>
    ∑ i ∈ S n, G n i ω * V n i ω
  dsimp only
  intro hL1
  have hEach : ∀ n : ℕ,
      Integrable (F n) P ∧ (∫ ω, F n ω ∂P) = 0 := by
    intro n
    have hOne :=
      avram_wave7_05_turn6_original_allnu_source_gaussian_multistop_gradient_automatic_L2_mean_zero
        X Y hYν hYσ Jsmall Jlarge hSourceDecomp
        x D hD w C hw q T
        (S n) (τ n) (hτ n) (B n) (hbounded n)
        (h n) (G n) (hGsource n)
        (K n) (hK n) (hGbound n)
    dsimp only at hOne
    exact hOne
  have hIntegrable : ∀ n : ℕ, Integrable (F n) P :=
    fun n => (hEach n).1
  have hT :=
    tendsto_integral_of_L1 M hMI.aestronglyMeasurable
      (Filter.Eventually.of_forall hIntegrable) hL1
  have hZeroFun : (fun n : ℕ => ∫ ω, F n ω ∂P) =
      (fun _ : ℕ => (0 : ℝ)) := by
    funext n
    exact (hEach n).2
  rw [hZeroFun] at hT
  have hConst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds (0 : ℝ)) :=
    tendsto_const_nhds
  exact (tendsto_nhds_unique hConst hT).symm
