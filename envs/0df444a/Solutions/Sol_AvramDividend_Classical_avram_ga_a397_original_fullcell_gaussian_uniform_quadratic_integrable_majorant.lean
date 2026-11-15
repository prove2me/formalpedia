-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a397_original_fullcell_gaussian_uniform_quadratic_integrable_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:04:37.710192+00:00
-- url     : https://prove2.me/submissions/e01c7637-9559-46b5-bd62-ae2dd8ff57f8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a400_zerojump_centred_source_horizon_sup_square_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option maxHeartbeats 800000

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0) (n : ℕ) :
    ∃ B : Ω → ℝ, Integrable B P ∧
      (∀ᵐ ω ∂P, 0 ≤ B ω) ∧
      (∀ (m : ℕ), ∀ᵐ ω ∂P, ∀ i : ℕ, i < m →
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let z : ℝ := X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
        |z| + z^2 + (Δ : ℝ) ≤ B ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨S,hSI,hS⟩ :=
    avram_ga_a400_zerojump_centred_source_horizon_sup_square_integrable
      X hNuZero (n : ℝ≥0)
  let B : Ω → ℝ := fun ω => (1 + (n : ℝ)) + 8 * S ω
  have hBI : Integrable B P :=
    (integrable_const _).add (hSI.const_mul 8)
  refine ⟨B, hBI, ?_, ?_⟩
  · filter_upwards [hS] with ω hω
    dsimp [B]
    nlinarith [hω.1]
  · intro m
    filter_upwards [hS] with ω hω
    intro i hi Δ s z
    have hΔ : 0 ≤ (Δ : ℝ) := by positivity
    have hpos : (0 : ℝ≥0) < (m : ℝ≥0) + 1 := by positivity
    have hupper : s + Δ ≤ (n : ℝ≥0) := by
      have hidx : ((i : ℝ≥0) + 1) ≤ ((m : ℝ≥0) + 1) := by
        exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt hi)
      calc
        s + Δ = ((i : ℝ≥0) + 1) * Δ := by
          dsimp [s]; ring
        _ ≤ ((m : ℝ≥0) + 1) * Δ := by
          gcongr
        _ = n := by
          dsimp [Δ]
          field_simp
    have hsbound : s ≤ (n : ℝ≥0) := by
      exact le_trans (le_add_of_nonneg_right bot_le) hupper
    let A : ℝ := X.X (s + Δ) ω - ((s + Δ : ℝ≥0) : ℝ) * X.c
    let C : ℝ := X.X s ω - (s : ℝ) * X.c
    have hA : A^2 ≤ S ω := hω.2 (s + Δ) hupper
    have hC : C^2 ≤ S ω := hω.2 s hsbound
    have hz : z = A - C := by
      dsimp [z, A, C]
      push_cast
      ring
    have hQuad : z^2 ≤ 4 * S ω := by
      rw [hz]
      nlinarith [sq_nonneg (A+C), hA, hC]
    have hAbs : |z| ≤ 1 + z^2 := by
      nlinarith [sq_nonneg (|z| - 1), sq_abs z]
    have hd : (Δ : ℝ) ≤ (n : ℝ) := by
      have hsmall : Δ ≤ (n : ℝ≥0) := by
        calc
          Δ ≤ s + Δ := le_add_of_nonneg_left bot_le
          _ ≤ n := hupper
      exact_mod_cast hsmall
    dsimp [B]
    nlinarith [hQuad, hAbs, hd]
