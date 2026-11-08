-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_zero_nu_original_discounted_gaussian_mesh_L1_limit_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:41:49.75314+00:00
-- url     : https://prove2.me/submissions/5c1edbfc-f5ee-4af9-a084-d0768cc447be

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn6_original_allnu_sameX_gaussian_bounded_C2_mesh_L1_mean_zero
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The genuine zero-negative-jump Gaussian physical-mesh term stays centred
under an L1 passage to its original-process stopped Itô limit. -/
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
    (h : ℕ → ι → ℝ≥0) (G : ℕ → ι → Ω → ℝ)
    (hGsource : ∀ n, ∀ i ∈ S n, G n i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n i ω : WithTop ℝ≥0)))
    (hGglobal : ∀ n, ∀ i ∈ S n, Measurable (G n i))
    (K : ℕ → ι → ℝ) (hK : ∀ n, ∀ i ∈ S n, 0 ≤ K n i)
    (hGbound : ∀ n, ∀ i ∈ S n, ∀ ω, |G n i ω| ≤ K n i)
    (M : Ω → ℝ) (hMI : Integrable M P) :
    let F : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ S n, G n i ω *
        (X.X (τ n i ω + h n i) ω -
          X.X (τ n i ω) ω - (h n i : ℝ) * X.c)
    Tendsto (fun n => ∫⁻ ω, ‖F n ω - M ω‖ₑ ∂P) atTop (nhds 0) →
      (∫ ω, M ω ∂P) = 0 := by
  have hSource : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (X.X t ω - (t : ℝ) * X.c) + (0 : ℝ) + (0 : ℝ) := by
    intro t ω
    ring
  have hMain :=
    avram_wave7_05_turn6_original_allnu_sameX_gaussian_bounded_C2_mesh_L1_mean_zero
      X X hν rfl (fun _ _ => 0) (fun _ _ => 0) hSource
      x D hD w C hw q T S τ hτ B hbounded h G hGsource
      hGglobal K hK hGbound M hMI
  simpa only using hMain
