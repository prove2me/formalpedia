-- Prove2me | solution 2 for AvramDividend.Classical.levy_capped_upcrossing_compensated_exp_second_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:05:41.746651+00:00
-- url     : https://prove2.me/submissions/8cd89f6c-a54e-4e1f-afb3-72601ff1518e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_upper_grid_stopped_exp_integrable
import Theorems.Thm_AvramDividend_Classical_levy_capped_upper_grid_exp_moment_one

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (θ : ℝ) (hθ : 0 ≤ θ) (z : ℝ) (m : ℕ) :
    (∫ ω,
      let K := hittingBtwn (fun k ω => X.X (clock k) ω) (Ioi z) 0 m ω
      (Real.exp (θ * X.X (clock K) ω -
        (clock K : ℝ) * X.ψ θ)) ^ 2 ∂P) ≤
    Real.exp ((clock m : ℝ) *
      max (X.ψ (2 * θ) - 2 * X.ψ θ) 0) := by
  set d := max (X.ψ (2 * θ) - 2 * X.ψ θ) 0 with hd
  set C := Real.exp ((clock m : ℝ) * d) with hC
  have h2 : (0:ℝ) ≤ 2 * θ := by linarith
  have hint := AvramDividend.Classical.levy_upper_grid_stopped_exp_integrable X clock hc H hH
    (2 * θ) h2 z m (fun ω => hittingBtwn (fun k ω => X.X (clock k) ω) (Ioi z) 0 m ω) (fun _ => rfl)
  have hone := AvramDividend.Classical.levy_capped_upper_grid_exp_moment_one X clock hc hc0 H hH
    (2 * θ) h2 z m
  have hle : ∀ ω, (let K := hittingBtwn (fun k ω => X.X (clock k) ω) (Ioi z) 0 m ω
      (Real.exp (θ * X.X (clock K) ω - (clock K : ℝ) * X.ψ θ)) ^ 2) ≤
      (let K := hittingBtwn (fun k ω => X.X (clock k) ω) (Ioi z) 0 m ω
      Real.exp (2 * θ * X.X (clock K) ω - (clock K : ℝ) * X.ψ (2 * θ))) * C := by
    intro ω
    simp only
    set K := hittingBtwn (fun k ω => X.X (clock k) ω) (Ioi z) 0 m ω
    have hK : K ≤ m := hittingBtwn_le ω
    have hcK : (clock K : ℝ) ≤ clock m := by exact_mod_cast hc hK
    have hcK0 : (0:ℝ) ≤ clock K := (clock K).2
    rw [← Real.exp_nat_mul, hC, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : X.ψ (2 * θ) - 2 * X.ψ θ ≤ d := le_max_left _ _
    have h0 : 0 ≤ d := le_max_right _ _
    have : (clock K : ℝ) * (X.ψ (2 * θ) - 2 * X.ψ θ) ≤ clock m * d :=
      le_trans (mul_le_mul_of_nonneg_left h1 hcK0) (mul_le_mul_of_nonneg_right hcK h0)
    push_cast
    nlinarith
  calc _ ≤ ∫ ω, (let K := hittingBtwn (fun k ω => X.X (clock k) ω) (Ioi z) 0 m ω
      Real.exp (2 * θ * X.X (clock K) ω - (clock K : ℝ) * X.ψ (2 * θ))) * C ∂P := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun ω => by simp only; positivity)
        · exact hint.mul_const C
        · exact Filter.Eventually.of_forall hle
    _ = C := by rw [integral_mul_const, hone, one_mul]
