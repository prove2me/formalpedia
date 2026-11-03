-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn4_original_controlled_grid_gradient_exact_L2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:49:01.328257+00:00
-- url     : https://prove2.me/submissions/b8ac53fd-dc19-4eef-acf7-8110bf300930

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_controlled_stopped_gaussian_exact_variance
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_finite_predictable_grid_exact_L2_isometry

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
    (G : ι → Ω → ℝ)
    (hGsource : ∀ i ∈ S, G i = stoppedValue (fun u ω =>
      if u ≤ T then
        (Real.exp (-(q * (u : ℝ))) *
          deriv w (Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u)) *
          (if (u : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun _ => (s i : WithTop ℝ≥0)))
    (hGown : ∀ i ∈ S, Measurable[𝓕.rightCont (s i)] (G i))
    (hGpair : ∀ i ∈ S, ∀ j ∈ S, t i ≤ s j →
      Measurable[𝓕.rightCont (s j)] (G i))
    (K : ℝ) (hK : 0 ≤ K)
    (hGbound : ∀ i ∈ S, ∀ ω, |G i ω| ≤ K) :
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * (X.X (t i) ω - X.X (s i) ω -
        ((t i - s i) : ℝ) * X.c)
    MemLp (fun ω => ∑ i ∈ S, F i ω) 2 P ∧
    Integrable (fun ω => (∑ i ∈ S, F i ω) ^ 2) P ∧
    (∫ ω, (∑ i ∈ S, F i ω) ^ 2 ∂P) =
      ∑ i ∈ S, (∫ ω, (F i ω) ^ 2 ∂P) := by
  classical
  let F : ι → Ω → ℝ := fun i ω =>
    G i ω * (X.X (t i) ω - X.X (s i) ω -
      ((t i - s i) : ℝ) * X.c)
  have hLp : ∀ i ∈ S, MemLp (F i) 2 P := by
    intro i hi
    have hτ : ∀ r : ℝ≥0,
        MeasurableSet[𝓕.rightCont r]
          {ω : Ω | (fun _ : Ω => s i) ω ≤ r} := by
      intro r
      by_cases hsr : s i ≤ r
      · simpa [hsr]
      · simpa [hsr]
    have hbound : ∀ ω : Ω, |(stoppedValue (fun u ω =>
        if u ≤ T then
          (Real.exp (-(q * (u : ℝ))) *
            deriv w (Function.leftLim
              (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u)) *
            (if (u : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) (fun _ => (s i : WithTop ℝ≥0))) ω| ≤ K := by
      intro ω
      simpa only [← hGsource i hi] using hGbound i hi ω
    have hOne :=
      avram_wave7_05_turn3_original_controlled_stopped_gaussian_exact_variance
        X hν x D hD w q T (fun _ : Ω => s i) hτ (s i)
        (fun _ => le_refl (s i)) (t i - s i) K hK hbound
    dsimp only at hOne
    have heq : s i + (t i - s i) = t i :=
      add_tsub_cancel_of_le (hst i hi)
    simpa only [F, hGsource i hi, heq, NNReal.coe_sub (hst i hi)] using hOne.1
  have hGrid :=
    avram_wave7_05_original_gaussian_finite_predictable_grid_exact_L2_isometry
      X hν S s t G hst hSep hGown hGpair hLp
  dsimp only at hGrid
  exact hGrid
