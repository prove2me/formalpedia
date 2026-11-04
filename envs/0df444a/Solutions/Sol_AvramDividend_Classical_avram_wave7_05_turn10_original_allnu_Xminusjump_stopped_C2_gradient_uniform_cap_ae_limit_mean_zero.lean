-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn10_original_allnu_Xminusjump_stopped_C2_gradient_uniform_cap_ae_limit_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:48:14.843464+00:00
-- url     : https://prove2.me/submissions/88ae0e94-b38b-4245-ac0c-f55ec117efc2

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_L2_isometry
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn10_original_allnu_Xminusjump_stopped_C2_gradient_uniform_cap_L2_seminorm_bound
import Theorems.Thm_AvramDividend_Classical_uniformIntegrable_one_of_uniform_l2_seminorm_bound
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.LeftRightLim

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

/-! Original stopped C2 Gaussian gradient cap and a.e. limit yield zero mean. -/
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
    (hGbound : ∀ n ω, |G n ω| ≤ K)
    (L : Ω → ℝ) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    let V : ℕ → Ω → ℝ := fun n ω =>
      M (τ n ω + h n) ω - M (τ n ω) ω
    (∀ᵐ ω ∂P, Tendsto (fun n => G n ω * V n ω) atTop (nhds (L ω))) →
      (∫ ω, L ω ∂P) = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
  let V : ℕ → Ω → ℝ := fun n ω =>
    M (τ n ω + h n) ω - M (τ n ω) ω
  let Q : ℕ → Ω → ℝ := fun n ω => G n ω * V n ω
  change (∀ᵐ ω ∂P, Tendsto (fun n => Q n ω) atTop (nhds (L ω))) →
    (∫ ω, L ω ∂P) = 0
  intro hConv
  have hL2 :=
    avram_wave7_05_turn10_original_allnu_Xminusjump_stopped_C2_gradient_uniform_cap_L2_seminorm_bound
      X Y hYν hYσ Jsmall Jlarge hSourceDecomp
      x D hD w C hw q T τ hτ B hbounded h hStep G hGsource K hK hGbound
  dsimp only at hL2
  have hEach : ∀ n : ℕ,
      Integrable (Q n) P ∧ (∫ ω, Q n ω ∂P) = 0 := by
    intro n
    have hOne :=
      avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_L2_isometry
        X Y hYν hYσ Jsmall Jlarge hSourceDecomp
        x D hD w C hw q T (τ n) (hτ n) (B n) (hbounded n)
        (h n) (G n) (hGsource n) K hK (hGbound n)
    dsimp only at hOne
    exact ⟨hOne.2.1, hOne.2.2.1⟩
  have hMeas : ∀ n, AEStronglyMeasurable (Q n) P :=
    fun n => (hEach n).1.aestronglyMeasurable
  let C₂ : ℝ≥0 :=
    ⟨Real.sqrt ((T : ℝ) * X.σ ^ 2 * K ^ 2), Real.sqrt_nonneg _⟩
  have hL2NN : ∀ n, eLpNorm (Q n) (2 : ℝ≥0∞) P ≤
      (C₂ : ℝ≥0∞) := by
    intro n
    calc
      eLpNorm (Q n) (2 : ℝ≥0∞) P ≤
          ENNReal.ofReal (Real.sqrt ((T : ℝ) * X.σ ^ 2 * K ^ 2)) := hL2 n
      _ = (C₂ : ℝ≥0∞) := by
        change ENNReal.ofReal (Real.sqrt ((T : ℝ) * X.σ ^ 2 * K ^ 2)) =
          ENNReal.ofNNReal
            ⟨Real.sqrt ((T : ℝ) * X.σ ^ 2 * K ^ 2), Real.sqrt_nonneg _⟩
        exact ENNReal.ofReal_eq_coe_nnreal
          (Real.sqrt_nonneg ((T : ℝ) * X.σ ^ 2 * K ^ 2))
  have hUI : UniformIntegrable Q (1 : ℝ≥0∞) P :=
    uniformIntegrable_one_of_uniform_l2_seminorm_bound
      P Q C₂ hMeas hL2NN
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
  exact (tendsto_nhds_unique tendsto_const_nhds hT).symm
