-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn4_original_controlled_grid_gradient_auto_predictable_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:02:00.670263+00:00
-- url     : https://prove2.me/submissions/f3fdb145-f3b9-4d47-b853-b2dbb76225ee

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_stopped_discounted_deriv_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn4_original_controlled_grid_gradient_exact_L2_isometry

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (T : ℝ≥0)
    (S : Finset ι) (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → t i ≤ s j ∨ t j ≤ s i)
    (K : ℝ) (hK : 0 ≤ K)
    (hGbound : ∀ i ∈ S, ∀ ω : Ω,
      |(if s i ≤ T then
        (Real.exp (-(q * (s i : ℝ))) *
          deriv w (Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) (s i))) *
        (if (s i : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0)| ≤ K) :
    let G : ι → Ω → ℝ := fun i ω =>
      if s i ≤ T then
        (Real.exp (-(q * (s i : ℝ))) *
          deriv w (Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) (s i))) *
        (if (s i : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * (X.X (t i) ω - X.X (s i) ω -
        ((t i - s i) : ℝ) * X.c)
    MemLp (fun ω => ∑ i ∈ S, F i ω) 2 P ∧
    Integrable (fun ω => (∑ i ∈ S, F i ω) ^ 2) P ∧
    (∫ ω, (∑ i ∈ S, F i ω) ^ 2 ∂P) =
      ∑ i ∈ S, (∫ ω, (F i ω) ^ 2 ∂P) := by
  classical
  let Z : ℝ≥0 → Ω → ℝ := fun u ω =>
    if u ≤ T then
      (Real.exp (-(q * (u : ℝ))) *
        deriv w (Function.leftLim
          (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u)) *
      (if (u : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
    else 0
  let G : ι → Ω → ℝ := fun i ω => Z (s i) ω
  let F : ι → Ω → ℝ := fun i ω =>
    G i ω * (X.X (t i) ω - X.X (s i) ω -
      ((t i - s i) : ℝ) * X.c)
  have hPred : IsStronglyPredictable 𝓕.rightCont Z :=
    avram_wave3_04_source_stopped_discounted_deriv_predictable
      X x D hD w q T
  have hGsource : ∀ i ∈ S, G i =
      stoppedValue Z (fun _ : Ω => (s i : WithTop ℝ≥0)) := by
    intro i hi
    funext ω
    rfl
  have hGown : ∀ i ∈ S,
      Measurable[𝓕.rightCont (s i)] (G i) := by
    intro i hi
    exact (hPred.stronglyAdapted (s i)).measurable
  have hGpair : ∀ i ∈ S, ∀ j ∈ S, t i ≤ s j →
      Measurable[𝓕.rightCont (s j)] (G i) := by
    intro i hi j hj hij
    exact (hGown i hi).mono
      ((𝓕.rightCont).mono (le_trans (hst i hi) hij)) le_rfl
  have hResult :=
    avram_wave7_05_turn4_original_controlled_grid_gradient_exact_L2_isometry
      X hν x D hD w q T S s t hst hSep G
      hGsource hGown hGpair K hK hGbound
  dsimp only at hResult
  exact hResult
