-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_finitecap_physical_Hessian_cross_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T17:41:26.074279+00:00
-- url     : https://prove2.me/submissions/f161cdb6-7288-4172-8919-134e22091744

import Theorems.Thm_AvramDividend_Classical_avram_ga_original_bounded_Hessian_true_physical_fullcell_cross_abs_L1
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (b q : ℝ)
    (hBound : ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : ℕ) (ω : Ω) (i : ℕ),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      i < m → s < ρ ω → s + Δ ≤ ρ ω →
      |Real.exp (-(q * (s : ℝ))) *
        (if x + X.X s ω - rightLimit D s ω ≤ b
        then iteratedDeriv 2 w (x + X.X s ω - rightLimit D s ω)
        else 0)| ≤ K) :
    let B : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (Finset.range m).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let R : ℝ := X.X (s + Δ) ω - X.X s ω
        let Z : ℝ := R - (Δ : ℝ) * X.c
        if s < ρ ω ∧ s + Δ ≤ ρ ω then
          Real.exp (-(q * (s : ℝ))) *
            (if x + X.X s ω - rightLimit D s ω ≤ b
             then iteratedDeriv 2 w (x + X.X s ω - rightLimit D s ω)
             else 0) / 2 * (R ^ 2 - Z ^ 2)
        else 0)
    (∀ m, Integrable (fun ω => |B m ω|) P) →
    Tendsto (fun m => ∫ ω, |B m ω| ∂P)
      atTop (nhds (0 : ℝ)) := by
  classical
  obtain ⟨K, hK, hCoef⟩ := hBound
  intro B hBI
  let H : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    if s < ρ ω ∧ s + Δ ≤ ρ ω then
      Real.exp (-(q * (s : ℝ))) *
        (if x + X.X s ω - rightLimit D s ω ≤ b
         then iteratedDeriv 2 w (x + X.X s ω - rightLimit D s ω)
         else 0)
    else 0
  have hH : ∀ m ω i, i < m → |H m i ω| ≤ K := by
    intro m ω i hi
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    by_cases hc : s < ρ ω ∧ s + Δ ≤ ρ ω
    · simpa only [H, Δ, s, if_pos hc] using
        (hCoef m ω i hi hc.1 hc.2)
    · simpa only [H, Δ, s, if_neg hc, abs_zero] using hK
  let S : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    (Finset.range m).sum (fun i =>
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let R : ℝ := X.X (s + Δ) ω - X.X s ω
      let Z : ℝ := R - (Δ : ℝ) * X.c
      if s < ρ ω ∧ s + Δ ≤ ρ ω then
        H m i ω / 2 * (R ^ 2 - Z ^ 2) else 0)
  have hEq (m : ℕ) (ω : Ω) : S m ω = B m ω := by
    dsimp only [S, B]
    apply Finset.sum_congr rfl
    intro i hi
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    by_cases hc : s < ρ ω ∧ s + Δ ≤ ρ ω
    · simp [H, hc, Δ, s]
    · simp [H, hc, Δ, s]
  have hI : ∀ m, Integrable (fun ω => |S m ω|) P := by
    intro m
    have heq : (fun ω => |S m ω|) = (fun ω => |B m ω|) := by
      funext ω
      rw [hEq m ω]
    rw [heq]
    exact hBI m
  have hLimit : Tendsto (fun m => ∫ ω, |S m ω| ∂P)
      atTop (nhds (0 : ℝ)) := by
    simpa only [S] using
      (avram_ga_original_bounded_Hessian_true_physical_fullcell_cross_abs_L1
        X hNuZero n ρ hρstop H K hK hH hI)
  have hseq : (fun m => ∫ ω, |S m ω| ∂P) =
      (fun m => ∫ ω, |B m ω| ∂P) := by
    funext m
    simp only [hEq]
  exact hseq ▸ hLimit
