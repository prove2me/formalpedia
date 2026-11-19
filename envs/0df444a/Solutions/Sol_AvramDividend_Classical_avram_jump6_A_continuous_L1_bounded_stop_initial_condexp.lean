-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_continuous_L1_bounded_stop_initial_condexp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:59:08.037003+00:00
-- url     : https://prove2.me/submissions/b7babeb8-26f6-4d38-bb5b-cd17aed9d524

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_rightcont_upper_grid_stops
import Theorems.Thm_AvramDividend_Classical_avram_ja18_finite_range_optional_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_ja18_rightcontinuous_clock_composition
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_finite_range_stopped_mart_terminal_condexp
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_UI_condexp_family_original_clock_L1_limit
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_initial_condexp_zero_of_L1_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (G : ℝ≥0 → Ω → ℝ)
    (hAdapted : ∀ t : ℝ≥0, Measurable[𝓕.rightCont t] (G t))
    (hZero : ∀ᵐ ω ∂P, G 0 ω = 0)
    (hCont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => G t ω))
    (hInt : ∀ t : ℝ≥0, Integrable (G t) P)
    (hCond : ∀ s t : ℝ≥0, s ≤ t →
       ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (G t) ω = G s ω)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0)) :
    Integrable (fun ω => G (τ ω) ω) P ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P
        (fun ω => G (τ ω) ω) ω = 0) := by
  classical
  obtain ⟨ρ, hStop, hRange, hAbove, hBelow, hConv⟩ :=
    avram_ja18_original_rightcont_upper_grid_stops τ hτstop n hτbound
  let V : ℕ → Ω → ℝ := fun k ω => G (ρ k ω) ω
  have hGrid (k : ℕ) :
      Integrable (V k) P ∧
      (P[V k | 𝓕.rightCont 0] =ᵐ[P] (fun _ : Ω => (0 : ℝ))) := by
    obtain ⟨S, hS⟩ := hRange k
    exact avram_ja18_finite_range_optional_condexp_zero
      G (ρ k) (n : ℝ≥0) (hStop k) (hBelow k)
      S hS hInt hCond hZero
  have hMeas (k : ℕ) :
      (hStop k).measurableSpace ≤ mΩ := by
    have hBound : ∀ ω, (ρ k ω : WithTop ℝ≥0) ≤ (n : WithTop ℝ≥0) := by
      intro ω
      exact_mod_cast hBelow k ω
    exact (hStop k).measurableSpace_le_of_le hBound
  have hCE (k : ℕ) :
      V k =ᵐ[P] P[G (n : ℝ≥0) | (hStop k).measurableSpace] := by
    obtain ⟨S, hS⟩ := hRange k
    exact avram_jump6_A_finite_range_stopped_mart_terminal_condexp
      G hAdapted hInt hCond n (ρ k) (hStop k) (hBelow k) S hS
  have hRight : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun u : ℝ≥0 => G u ω) (Set.Ici t) t := by
    filter_upwards [hCont] with ω hω
    intro t
    exact (hω.continuousAt).continuousWithinAt
  have hValueConv : ∀ᵐ ω ∂P,
      Tendsto (fun k => V k ω) atTop (nhds (G (τ ω) ω)) :=
    avram_ja18_rightcontinuous_clock_composition
      G τ ρ hRight hAbove hConv
  obtain ⟨hStopInt, hL1⟩ :=
    avram_jump6_A_UI_condexp_family_original_clock_L1_limit
      (G (n : ℝ≥0)) (hInt (n : ℝ≥0)) V
      (fun k => (hStop k).measurableSpace) hMeas hCE
      (fun ω => G (τ ω) ω) hValueConv
  have hL1Rev : Tendsto
      (fun k => eLpNorm (fun ω => G (τ ω) ω - V k ω) 1 P)
      atTop (nhds 0) := by
    have hEq : (fun k => eLpNorm
        (fun ω => G (τ ω) ω - V k ω) 1 P) =
        (fun k => eLpNorm
        (fun ω => V k ω - G (τ ω) ω) 1 P) := by
      funext k
      change eLpNorm ((fun ω => G (τ ω) ω) - V k) 1 P =
        eLpNorm (V k - (fun ω => G (τ ω) ω)) 1 P
      exact eLpNorm_sub_comm _ _ 1 P
    rw [hEq]
    exact hL1
  have hCenter :=
    avram_jump6_A_initial_condexp_zero_of_L1_limit
      (𝓕.rightCont 0) (𝓕.rightCont.le 0)
      V (fun ω => G (τ ω) ω)
      (fun k => (hGrid k).1) hStopInt
      (fun k => (hGrid k).2) hL1Rev
  exact ⟨hStopInt, hCenter⟩
