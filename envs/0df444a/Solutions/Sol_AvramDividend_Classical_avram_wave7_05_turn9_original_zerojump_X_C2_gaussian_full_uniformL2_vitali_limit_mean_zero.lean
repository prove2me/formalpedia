-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn9_original_zerojump_X_C2_gaussian_full_uniformL2_vitali_limit_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:16:41.760702+00:00
-- url     : https://prove2.me/submissions/dea9434f-3332-466c-833f-59f4ef47d696

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_zerojump_X_C2_gaussian_full_finite_ito_mesh_mean_zero
import Theorems.Thm_AvramDividend_Classical_uniformIntegrable_one_of_uniform_l2_seminorm_bound
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Direct original zerojump X controlled C2 Gaussian uniform L2/Vitali limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (S : ℕ → Finset ι) (τ : ℕ → ι → Ω → ℝ≥0)
    (hτ : ∀ n, ∀ i ∈ S n, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n i ω ≤ s})
    (B : ℕ → ι → ℝ≥0)
    (hbounded : ∀ n, ∀ i ∈ S n, ∀ ω, τ n i ω ≤ B n i)
    (h : ℕ → ι → ℝ≥0) (G H : ℕ → ι → Ω → ℝ)
    (hGsource : ∀ n, ∀ i ∈ S n, G n i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n i ω : WithTop ℝ≥0)))
    (hHsource : ∀ n, ∀ i ∈ S n, H n i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n i ω : WithTop ℝ≥0)))
    (BG BH : ℕ → ι → ℝ)
    (hBG : ∀ n, ∀ i ∈ S n, 0 ≤ BG n i)
    (hBH : ∀ n, ∀ i ∈ S n, 0 ≤ BH n i)
    (hGbound : ∀ n, ∀ i ∈ S n, ∀ ω, |G n i ω| ≤ BG n i)
    (hHbound : ∀ n, ∀ i ∈ S n, ∀ ω, |H n i ω| ≤ BH n i)
    (L : Ω → ℝ) (C₂ : ℝ≥0) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c
    let V : ℕ → ι → Ω → ℝ := fun n i ω =>
      M (τ n i ω + h n i) ω - M (τ n i ω) ω
    let Q : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ S n,
        (G n i ω * V n i ω + (1 / 2 : ℝ) * H n i ω *
          (V n i ω ^ 2 - (h n i : ℝ) * X.σ ^ 2))
    (∀ n, eLpNorm (Q n) (2 : ℝ≥0∞) P ≤ C₂) →
    (∀ᵐ ω ∂P, Tendsto (fun n => Q n ω) atTop (nhds (L ω))) →
    (∫ ω, L ω ∂P) = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c
  let V : ℕ → ι → Ω → ℝ := fun n i ω =>
    M (τ n i ω + h n i) ω - M (τ n i ω) ω
  let W : ℕ → ι → Ω → ℝ := fun n i ω =>
    X.X (τ n i ω + h n i) ω - X.X (τ n i ω) ω -
      (h n i : ℝ) * X.c
  have hV : V = W := by
    funext n i ω
    dsimp [V, W, M]
    push_cast
    ring
  let Q : ℕ → Ω → ℝ := fun n ω =>
    ∑ i ∈ S n, (G n i ω * V n i ω +
      (1 / 2 : ℝ) * H n i ω *
        (V n i ω ^ 2 - (h n i : ℝ) * X.σ ^ 2))
  change (∀ n, eLpNorm (Q n) (2 : ℝ≥0∞) P ≤ C₂) →
    (∀ᵐ ω ∂P, Tendsto (fun n => Q n ω) atTop (nhds (L ω))) →
    (∫ ω, L ω ∂P) = 0
  intro hL2 hConv
  have hEach : ∀ n : ℕ,
      Integrable (Q n) P ∧ (∫ ω, Q n ω ∂P) = 0 := by
    intro n
    have hOne :=
      avram_wave7_05_turn7_original_zerojump_X_C2_gaussian_full_finite_ito_mesh_mean_zero
        X hν x D hD w C hw
        q T (S n) (τ n) (hτ n) (B n) (hbounded n)
        (h n) (G n) (H n) (hGsource n) (hHsource n)
        (BG n) (BH n) (hBG n) (hBH n)
        (hGbound n) (hHbound n)
    dsimp only at hOne
    simpa only [Q, hV, W] using hOne
  have hMeas : ∀ n, AEStronglyMeasurable (Q n) P :=
    fun n => (hEach n).1.aestronglyMeasurable
  have hUI : UniformIntegrable Q (1 : ℝ≥0∞) P :=
    uniformIntegrable_one_of_uniform_l2_seminorm_bound
      P Q C₂ hMeas hL2
  have hLI : Integrable L P := hUI.integrable_of_ae_tendsto hConv
  have hLp : MemLp L 1 P := memLp_one_iff_integrable.mpr hLI
  have hv : Tendsto (fun n => eLpNorm (Q n - L) 1 P)
      atTop (nhds (0 : ℝ≥0∞)) :=
    tendsto_Lp_finite_of_tendsto_ae
      (by norm_num) (by norm_num)
      (fun n => hUI.1 n) hLp hUI.2.1 hConv
  have hv' : Tendsto (fun n => ∫⁻ ω, ‖Q n ω - L ω‖ₑ ∂P)
      atTop (nhds (0 : ℝ≥0∞)) := by
    simpa only [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] using hv
  have hT : Tendsto (fun n => ∫ ω, Q n ω ∂P)
      atTop (nhds (∫ ω, L ω ∂P)) :=
    tendsto_integral_of_L1 L hLI.aestronglyMeasurable
      (Eventually.of_forall (fun n => (hEach n).1)) hv'
  have hZeroFun : (fun n : ℕ => ∫ ω, Q n ω ∂P) =
      (fun _ : ℕ => (0 : ℝ)) := by
    funext n
    exact (hEach n).2
  rw [hZeroFun] at hT
  have hConst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds (0 : ℝ)) :=
    tendsto_const_nhds
  exact (tendsto_nhds_unique hConst hT).symm
