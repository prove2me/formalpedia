-- Prove2me | solution 1 for AvramDividend.Classical.levy_capped_upper_grid_crossing_compensated_exp_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T13:01:30.120112+00:00
-- url     : https://prove2.me/submissions/6bf3695c-934f-4eeb-8091-42c3b6c9fed2

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_capped_upper_grid_exp_moment_one
import Theorems.Thm_AvramDividend_Classical_levy_upper_grid_stopped_exp_integrable
import Theorems.Thm_AvramDividend_Classical_levy_capped_upper_grid_nohit_discounted_remainder_bound
import Mathlib.Probability.Process.HittingTime
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- Exact stopped exponential budget gives a crossing lower bound after no-hit removal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (θ q : ℝ) (hθ : 0 ≤ θ) (hroot : X.ψ θ = q)
    (z : ℝ) (m : ℕ) :
    1 - Real.exp (θ * z - (clock m : ℝ) * q) ≤
    (∫ ω, (if ∀ j : ℕ, j ≤ m → X.X (clock j) ω ≤ z then
        (0 : ℝ)
      else
        let K := hittingBtwn (fun k η => X.X (clock k) η) (Ioi z) 0 m ω
        Real.exp (θ * X.X (clock K) ω - (clock K : ℝ) * X.ψ θ)) ∂P) := by
  let E : Ω → Prop := fun ω => ∀ j : ℕ, j ≤ m → X.X (clock j) ω ≤ z
  let K : Ω → ℕ := fun ω =>
    hittingBtwn (fun k η => X.X (clock k) η) (Ioi z) 0 m ω
  let Z : Ω → ℝ := fun ω =>
    Real.exp (θ * X.X (clock (K ω)) ω - (clock (K ω) : ℝ) * X.ψ θ)
  have hobs (j : ℕ) : Measurable (X.X (clock j)) :=
    (X.adapted (clock j)).mono (𝓕.le (clock j)) le_rfl
  have hE : MeasurableSet {ω | E ω} := by
    have hset : {ω | E ω} =
        ⋂ j : ℕ, ⋂ (_ : j ≤ m), {ω | X.X (clock j) ω ≤ z} := by
      ext ω
      simp [E]
    rw [hset]
    exact MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ =>
        (hobs j) measurableSet_Iic
  have hZ : Integrable Z P :=
    levy_upper_grid_stopped_exp_integrable X clock hc H hH θ hθ z m K
      (fun _ => rfl)
  have hNo : Integrable (fun ω => if E ω then Z ω else 0) P := by
    have heq : (fun ω => if E ω then Z ω else 0) =
        ({ω | E ω}.indicator Z) := by
      funext ω
      by_cases he : E ω <;> simp [Set.indicator, he]
    rw [heq]
    exact hZ.indicator hE
  have hHit : Integrable (fun ω => if E ω then 0 else Z ω) P := by
    have heq : (fun ω => if E ω then 0 else Z ω) =
        ({ω | E ω}ᶜ.indicator Z) := by
      funext ω
      by_cases he : E ω <;> simp [Set.indicator, he]
    rw [heq]
    exact hZ.indicator hE.compl
  have hsplit : (∫ ω, Z ω ∂P) =
      (∫ ω, if E ω then Z ω else 0 ∂P) +
      (∫ ω, if E ω then 0 else Z ω ∂P) := by
    calc
      (∫ ω, Z ω ∂P) =
          ∫ ω, ((if E ω then Z ω else 0) +
            (if E ω then 0 else Z ω)) ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω
          by_cases he : E ω <;> simp [he]
      _ = _ := integral_add hNo hHit
  have htotal : (∫ ω, Z ω ∂P) = 1 := by
    exact levy_capped_upper_grid_exp_moment_one
      X clock hc hc0 H hH θ hθ z m
  have hrem :
      (∫ ω, if E ω then Z ω else 0 ∂P) ≤
      Real.exp (θ * z - (clock m : ℝ) * q) := by
    exact levy_capped_upper_grid_nohit_discounted_remainder_bound
      X clock θ q hθ hroot z m
  change 1 - Real.exp (θ * z - (clock m : ℝ) * q) ≤
    (∫ ω, if E ω then 0 else Z ω ∂P)
  linarith
