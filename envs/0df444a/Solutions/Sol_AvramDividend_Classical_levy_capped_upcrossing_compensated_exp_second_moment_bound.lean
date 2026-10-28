-- Prove2me | solution 1 for AvramDividend.Classical.levy_capped_upcrossing_compensated_exp_second_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T09:05:21.367724+00:00
-- url     : https://prove2.me/submissions/ae100194-2c93-44ff-901f-d31b5c342be2

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_upper_grid_stopped_exp_integrable
import Theorems.Thm_AvramDividend_Classical_levy_capped_upper_grid_exp_moment_one
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Process.HittingTime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Bounded-grid optional stopping controls the compensated exponential's square. -/
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
  let K : Ω → ℕ := fun ω =>
    hittingBtwn (fun k ω => X.X (clock k) ω) (Ioi z) 0 m ω
  let E : ℝ → Ω → ℝ := fun α ω =>
    Real.exp (α * X.X (clock (K ω)) ω - (clock (K ω) : ℝ) * X.ψ α)
  let B : ℝ := Real.exp ((clock m : ℝ) * max (X.ψ (2 * θ) - 2 * X.ψ θ) 0)
  have hInt2 : Integrable (E (2 * θ)) P :=
    levy_upper_grid_stopped_exp_integrable X clock hc H hH
      (2 * θ) (by positivity) z m K (fun _ => rfl)
  have hUnit : (∫ ω, E (2 * θ) ω ∂P) = 1 := by
    simpa only [E, K] using (levy_capped_upper_grid_exp_moment_one
      X clock hc hc0 H hH (2 * θ) (by positivity) z m)
  have hbound (ω : Ω) : (E θ ω) ^ 2 ≤ B * E (2 * θ) ω := by
    have hKle : K ω ≤ m :=
      hittingBtwn_le (u := fun k ω => X.X (clock k) ω)
        (s := Ioi z) (n := 0) (m := m) ω
    have ht : (clock (K ω) : ℝ) ≤ (clock m : ℝ) := by
      exact_mod_cast hc hKle
    have ht0 : (0 : ℝ) ≤ (clock (K ω) : ℝ) := NNReal.coe_nonneg _
    have hd : X.ψ (2 * θ) - 2 * X.ψ θ ≤
        max (X.ψ (2 * θ) - 2 * X.ψ θ) 0 := le_max_left _ _
    have hm : (0 : ℝ) ≤
        max (X.ψ (2 * θ) - 2 * X.ψ θ) 0 := le_max_right _ _
    have h1 := mul_le_mul_of_nonneg_left hd ht0
    have h2 := mul_le_mul_of_nonneg_right ht hm
    have he :
        2 * (θ * X.X (clock (K ω)) ω - (clock (K ω) : ℝ) * X.ψ θ) ≤
        (clock m : ℝ) * max (X.ψ (2 * θ) - 2 * X.ψ θ) 0 +
          (2 * θ * X.X (clock (K ω)) ω -
            (clock (K ω) : ℝ) * X.ψ (2 * θ)) := by
      nlinarith [h1, h2]
    dsimp [E, B]
    calc
      (Real.exp (θ * X.X (clock (K ω)) ω -
          (clock (K ω) : ℝ) * X.ψ θ)) ^ 2 =
        Real.exp (2 * (θ * X.X (clock (K ω)) ω -
          (clock (K ω) : ℝ) * X.ψ θ)) := by
            rw [pow_two, ← Real.exp_add]
            congr 1
            ring
      _ ≤ Real.exp ((clock m : ℝ) * max (X.ψ (2 * θ) - 2 * X.ψ θ) 0 +
          (2 * θ * X.X (clock (K ω)) ω -
            (clock (K ω) : ℝ) * X.ψ (2 * θ))) := Real.exp_le_exp.mpr he
      _ = _ := by rw [Real.exp_add]
  have hIntB : Integrable (fun ω => B * E (2 * θ) ω) P := hInt2.const_mul B
  have hle : (∫ ω, (E θ ω)^2 ∂P) ≤ ∫ ω, B * E (2 * θ) ω ∂P :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun ω => sq_nonneg (E θ ω)))
      hIntB (Filter.Eventually.of_forall hbound)
  change (∫ ω, (E θ ω)^2 ∂P) ≤ B
  calc
    (∫ ω, (E θ ω)^2 ∂P) ≤ ∫ ω, B * E (2 * θ) ω ∂P := hle
    _ = B * ∫ ω, E (2 * θ) ω ∂P := integral_const_mul B _
    _ = B := by rw [hUnit, mul_one]
