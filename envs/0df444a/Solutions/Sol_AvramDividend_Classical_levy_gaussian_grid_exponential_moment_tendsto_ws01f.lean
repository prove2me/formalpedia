-- Prove2me | solution 1 for AvramDividend.Classical.levy_gaussian_grid_exponential_moment_tendsto_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:13:46.128649+00:00
-- url     : https://prove2.me/submissions/4f24988b-3db4-4953-a518-7f25d663494a

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_psi_quadratic_gaussian_limit_ws01f
import Theorems.Thm_AvramDividend_Classical_quadratic_exponent_gaussian_grid_mgf_limit_ws01f
import Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_eigenfunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (m k : ℕ) (hm : 0 < m) (hk : 0 < k) (C : ℝ)
    (t : ℕ → ℝ≥0)
    (ht : ∀ n : ℕ,
      (t n : ℝ) = 1 / (((m : ℝ) * ((n : ℝ) + 1)) ^ 2)) :
    Tendsto (fun n : ℕ =>
      ∫ ω, Real.exp
        (((k : ℝ) * ((n : ℝ) + 1)) *
          (X.X (t n) ω - C * (t n : ℝ))) ∂P)
      atTop (nhds
        (Real.exp ((X.σ ^ 2 / 2) * ((k : ℝ) / (m : ℝ)) ^ 2))) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hd (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity
  have hψ := levy_psi_quadratic_gaussian_limit_ws01f X
  have hlim :=
    quadratic_exponent_gaussian_grid_mgf_limit_ws01f
      X.ψ (X.σ ^ 2 / 2) C hψ m k hm hk
  have hEq (n : ℕ) :
      (∫ ω, Real.exp
        (((k : ℝ) * ((n : ℝ) + 1)) *
          (X.X (t n) ω - C * (t n : ℝ))) ∂P) =
      Real.exp
        (X.ψ ((k : ℝ) * ((n : ℝ) + 1)) /
            (((m : ℝ) * ((n : ℝ) + 1)) ^ 2) -
          (k : ℝ) * C / ((m : ℝ) ^ 2 * ((n : ℝ) + 1))) := by
    have hθ : 0 ≤ (k : ℝ) * ((n : ℝ) + 1) := by positivity
    have heig := levy_transition_exponential_eigenfunction X
      (t n) ((k : ℝ) * ((n : ℝ) + 1)) hθ (-C * (t n : ℝ))
    calc
      _ = (∫ ω, Real.exp
        (((k : ℝ) * ((n : ℝ) + 1)) *
          ((-C * (t n : ℝ)) + X.X (t n) ω)) ∂P) := by
          congr 1
          funext ω
          congr 1
          ring
      _ = Real.exp
          (((k : ℝ) * ((n : ℝ) + 1)) * (-C * (t n : ℝ))) *
          Real.exp ((t n : ℝ) *
            X.ψ ((k : ℝ) * ((n : ℝ) + 1))) := by
          simpa only [SpectrallyNegativeLevy.ψ] using heig
      _ = Real.exp
        (X.ψ ((k : ℝ) * ((n : ℝ) + 1)) /
            (((m : ℝ) * ((n : ℝ) + 1)) ^ 2) -
          (k : ℝ) * C / ((m : ℝ) ^ 2 * ((n : ℝ) + 1))) := by
          rw [← Real.exp_add]
          congr 1
          rw [ht n]
          field_simp [ne_of_gt hmR, ne_of_gt (hd n)] <;> ring
  have hfun :
      (fun n : ℕ =>
        ∫ ω, Real.exp
          (((k : ℝ) * ((n : ℝ) + 1)) *
            (X.X (t n) ω - C * (t n : ℝ))) ∂P) =
      (fun n : ℕ =>
        Real.exp
          (X.ψ ((k : ℝ) * ((n : ℝ) + 1)) /
              (((m : ℝ) * ((n : ℝ) + 1)) ^ 2) -
            (k : ℝ) * C / ((m : ℝ) ^ 2 * ((n : ℝ) + 1)))) := by
    funext n
    exact hEq n
  rw [hfun]
  exact hlim
