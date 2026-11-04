-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn11_original_allnu_C2_disjoint_grid_gaussian_auto_cell_total_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T11:07:57.285091+00:00
-- url     : https://prove2.me/submissions/4a74bde0-3446-4d46-8db3-ad539da8ff7b

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn11_original_allnu_C2_disjoint_grid_gaussian_total_time_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn11_original_allnu_stopped_C2_gradient_cell_sigma_time_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Uniform finite-grid L² control for the actual stopped original-process gradient. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (u : ℝ≥0) (ω : Ω),
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (S : Finset ℕ) (s t : ℕ → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      t i ≤ s j ∨ t j ≤ s i)
    (hTotal : (∑ i ∈ S, ((t i - s i) : ℝ≥0) : ℝ) ≤ (T : ℝ))
    (K : ℝ) (hK : 0 ≤ K)
    (hGsource : ∀ i ∈ S,
      (fun ω => if s i ≤ T then
        (Real.exp (-(q * (s i : ℝ))) *
          deriv w (Function.leftLim
            (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i))) *
        (if (s i : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) = stoppedValue (fun u ω =>
        if u ≤ T then
          (Real.exp (-(q * (u : ℝ))) *
            deriv w (Function.leftLim
              (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u)) *
          (if (u : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) (fun _ : Ω => (s i : WithTop ℝ≥0)))
    (hGbound : ∀ i ∈ S, ∀ ω,
      |if s i ≤ T then
        (Real.exp (-(q * (s i : ℝ))) *
          deriv w (Function.leftLim
            (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i))) *
        (if (s i : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0| ≤ K) :
    let G : ℕ → Ω → ℝ := fun i ω =>
      if s i ≤ T then
        (Real.exp (-(q * (s i : ℝ))) *
          deriv w (Function.leftLim
            (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i))) *
        (if (s i : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0
    let F : ℕ → Ω → ℝ := fun i ω =>
      G i ω * (Y.X (t i) ω - Y.X (s i) ω -
        ((t i - s i) : ℝ) * Y.c)
    MemLp (fun ω => ∑ i ∈ S, F i ω) 2 P ∧
      (∫ ω, (∑ i ∈ S, F i ω) ^ 2 ∂P) ≤
        (T : ℝ) * X.σ ^ 2 * K ^ 2 := by
  classical
  let G : ℕ → Ω → ℝ := fun i ω =>
    if s i ≤ T then
      (Real.exp (-(q * (s i : ℝ))) *
        deriv w (Function.leftLim
          (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i))) *
      (if (s i : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
    else 0
  let F : ℕ → Ω → ℝ := fun i ω =>
    G i ω * (Y.X (t i) ω - Y.X (s i) ω -
      ((t i - s i) : ℝ) * Y.c)
  let M : ℝ≥0 → Ω → ℝ := fun u ω =>
    X.X u ω - (u : ℝ) * X.c - Jsmall u ω - Jlarge u ω
  have hM (u : ℝ≥0) (ω : Ω) :
      M u ω = Y.X u ω - (u : ℝ) * Y.c := by
    dsimp [M]
    rw [hSourceDecomp u ω]
    ring
  have hStop (i : ℕ) (u : ℝ≥0) :
      MeasurableSet[𝓕.rightCont u] {ω : Ω | s i ≤ u} := by
    by_cases hh : s i ≤ u
    · simpa [hh] using
        (MeasurableSet.univ : MeasurableSet[𝓕.rightCont u] (Set.univ : Set Ω))
    · simpa [hh] using
        (MeasurableSet.empty : MeasurableSet[𝓕.rightCont u] (∅ : Set Ω))
  have hCellOne (i : ℕ) (hi : i ∈ S) :
      MemLp (F i) 2 P ∧
      (∫ ω, (F i ω) ^ 2 ∂P) ≤
        ((t i - s i) : ℝ) * X.σ ^ 2 * K ^ 2 := by
    have hLen : s i + (t i - s i) = t i := by
      simpa only [add_comm] using (tsub_add_cancel_of_le (hst i hi))
    have hOne :=
      avram_wave7_05_turn11_original_allnu_stopped_C2_gradient_cell_sigma_time_bound
        X Y hYν hYσ Jsmall Jlarge hSourceDecomp
        x D hD w C hw q T (fun _ : Ω => s i)
        (hStop i) (s i) (fun _ => le_rfl) (t i - s i)
        (G i) (hGsource i hi) K hK (hGbound i hi)
    dsimp only at hOne
    have hVEq (ω : Ω) :
        M (s i + (t i - s i)) ω - M (s i) ω =
        Y.X (t i) ω - Y.X (s i) ω -
          ((t i - s i) : ℝ) * Y.c := by
      rw [hLen, hM (t i) ω, hM (s i) ω]
      ring
    have hFfun :
        (fun ω => G i ω *
          (M (s i + (t i - s i)) ω - M (s i) ω)) = F i := by
      funext ω
      dsimp [F]
      rw [hVEq ω]
    constructor
    · rw [← hFfun]
      exact hOne.1
    · rw [← hFfun]
      simpa only [NNReal.coe_sub (hst i hi)] using hOne.2
  have hLp : ∀ i ∈ S, MemLp (F i) 2 P :=
    fun i hi => (hCellOne i hi).1
  have hCell : ∀ i ∈ S,
      (∫ ω, (F i ω) ^ 2 ∂P) ≤
        ((t i - s i) : ℝ) * X.σ ^ 2 * K ^ 2 :=
    fun i hi => (hCellOne i hi).2
  have hGrid :=
    avram_wave7_05_turn11_original_allnu_C2_disjoint_grid_gaussian_total_time_L2
      X Y hYν hYσ Jsmall Jlarge hSourceDecomp x D hD w C hw q T
      S s t hst hSep hTotal K hK hLp hCell
  dsimp only at hGrid
  exact hGrid
