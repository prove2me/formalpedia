-- Prove2me | solution 1 for AvramDividend.Classical.levy_capped_upper_grid_nohit_discounted_remainder_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T12:09:54.937276+00:00
-- url     : https://prove2.me/submissions/2d3005a4-dd3f-4459-bb9e-73f8d656b93f

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_hittingBtwn_eq_terminal_of_no_observed_crossing
import Mathlib.Probability.Process.HittingTime
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The capped exponential's no-upcrossing remainder is exponentially small. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hroot : X.ψ θ = q)
    (z : ℝ) (m : ℕ) :
    (∫ ω, (if ∀ j : ℕ, j ≤ m → X.X (clock j) ω ≤ z then
        let K := hittingBtwn (fun k η => X.X (clock k) η) (Ioi z) 0 m ω
        Real.exp (θ * X.X (clock K) ω - (clock K : ℝ) * X.ψ θ)
      else (0 : ℝ)) ∂P) ≤
    Real.exp (θ * z - (clock m : ℝ) * q) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let R : ℝ := Real.exp (θ * z - (clock m : ℝ) * q)
  have hpoint (ω : Ω) :
      (if ∀ j : ℕ, j ≤ m → X.X (clock j) ω ≤ z then
        let K := hittingBtwn (fun k η => X.X (clock k) η) (Ioi z) 0 m ω
        Real.exp (θ * X.X (clock K) ω - (clock K : ℝ) * X.ψ θ)
      else (0 : ℝ)) ≤ R := by
    by_cases hnone : ∀ j : ℕ, j ≤ m → X.X (clock j) ω ≤ z
    · have hK :
          hittingBtwn (fun k η => X.X (clock k) η) (Ioi z) 0 m ω = m :=
        chat03_hittingBtwn_eq_terminal_of_no_observed_crossing
          (fun k η => X.X (clock k) η) (Ioi z) ω m
          (by
            intro j hj
            exact not_lt.mpr (hnone j (Nat.le_of_lt hj)))
      have hmul : θ * X.X (clock m) ω ≤ θ * z :=
        mul_le_mul_of_nonneg_left (hnone m le_rfl) hθ
      have he :
          Real.exp (θ * X.X (clock m) ω - (clock m : ℝ) * q) ≤ R :=
        Real.exp_le_exp.mpr (sub_le_sub_right hmul _)
      rw [if_pos hnone]
      change Real.exp
        (θ * X.X (clock
          (hittingBtwn (fun k η => X.X (clock k) η) (Ioi z) 0 m ω)) ω -
        ((clock (hittingBtwn (fun k η => X.X (clock k) η)
          (Ioi z) 0 m ω) : ℝ≥0) : ℝ) * X.ψ θ) ≤ R
      rw [hK, hroot]
      exact he
    · rw [if_neg hnone]
      exact Real.exp_nonneg _
  have hnonneg (ω : Ω) :
      0 ≤ (if ∀ j : ℕ, j ≤ m → X.X (clock j) ω ≤ z then
        let K := hittingBtwn (fun k η => X.X (clock k) η) (Ioi z) 0 m ω
        Real.exp (θ * X.X (clock K) ω - (clock K : ℝ) * X.ψ θ)
      else (0 : ℝ)) := by
    by_cases hnone : ∀ j : ℕ, j ≤ m → X.X (clock j) ω ≤ z
    · rw [if_pos hnone]
      exact Real.exp_nonneg _
    · rw [if_neg hnone]
  have hRintegrable : Integrable (fun _ : Ω => R) P :=
    integrable_const R
  calc
    _ ≤ ∫ _ω : Ω, R ∂P :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall hnonneg)
        hRintegrable
        (Filter.Eventually.of_forall hpoint)
    _ = R := by simp
    _ = Real.exp (θ * z - (clock m : ℝ) * q) := rfl
