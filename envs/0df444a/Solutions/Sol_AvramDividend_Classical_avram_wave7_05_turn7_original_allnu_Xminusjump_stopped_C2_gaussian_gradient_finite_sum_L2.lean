-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn7_original_allnu_Xminusjump_stopped_C2_gaussian_gradient_finite_sum_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:21:31.056643+00:00
-- url     : https://prove2.me/submissions/b4fdc3cc-aa2f-457f-a6b5-456a1ca64576

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_stopped_gaussian_finite_bounded_predictable_gain_sum_L2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Bounded original C2 gradient finite Gaussian stopped sum is L2 on the exact source. -/
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
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (S : Finset ι)
    (h : ι → ℝ≥0) (G : ι → Ω → ℝ)
    (hGsource : ∀ i ∈ S, G i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0)))
    (K : ι → ℝ) (hK : ∀ i ∈ S, 0 ≤ K i)
    (hGbound : ∀ i ∈ S, ∀ ω, |G i ω| ≤ K i) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    MemLp (fun ω => ∑ i ∈ S,
      G i ω * (M (τ ω + h i) ω - M (τ ω) ω)) 2 P := by
  classical
  let M : ℝ≥0 → Ω → ℝ := fun t ω =>
    X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
  have hPred :=
    avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
      X x D hD w C hw q T τ hτ
  dsimp only at hPred
  have hGS : ∀ i ∈ S,
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        (G i) := by
    intro i hi
    rw [hGsource i hi]
    exact hPred.1
  have hGG : ∀ i ∈ S, Measurable (G i) := by
    intro i hi
    rw [hGsource i hi]
    exact hPred.2.2.1
  have hOne :=
    avram_wave7_05_original_stopped_gaussian_finite_bounded_predictable_gain_sum_L2
      Y hYν τ hτ B hbounded S h G hGS hGG K hK hGbound
  dsimp only at hOne
  have hM : ∀ t : ℝ≥0, ∀ ω : Ω,
      M t ω = Y.X t ω - (t : ℝ) * Y.c := by
    intro t ω
    dsimp [M]
    rw [hSourceDecomp t ω]
    ring
  have hF :
      (fun ω => ∑ i ∈ S,
        G i ω * (M (τ ω + h i) ω - M (τ ω) ω)) =
      (fun ω => ∑ i ∈ S,
        G i ω * (Y.X (τ ω + h i) ω -
          Y.X (τ ω) ω - (h i : ℝ) * Y.c)) := by
    funext ω
    apply Finset.sum_congr rfl
    intro i hi
    rw [hM (τ ω + h i) ω, hM (τ ω) ω]
    push_cast
    ring
  change MemLp (fun ω => ∑ i ∈ S,
    G i ω * (M (τ ω + h i) ω - M (τ ω) ω)) 2 P
  rw [hF]
  exact hOne
