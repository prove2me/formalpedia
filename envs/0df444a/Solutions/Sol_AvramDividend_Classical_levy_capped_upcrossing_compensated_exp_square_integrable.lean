-- Prove2me | solution 1 for AvramDividend.Classical.levy_capped_upcrossing_compensated_exp_square_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T09:22:10.198926+00:00
-- url     : https://prove2.me/submissions/04a1e6ad-88bd-47ca-9a91-22b1e6c87eeb

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_upper_grid_stopped_exp_integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Process.HittingTime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The capped-grid compensated Lévy exponential has an integrable square. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (θ : ℝ) (hθ : 0 ≤ θ) (z : ℝ) (m : ℕ) :
    Integrable (fun ω =>
      let K := hittingBtwn (fun k ω => X.X (clock k) ω) (Ioi z) 0 m ω
      (Real.exp (θ * X.X (clock K) ω -
        (clock K : ℝ) * X.ψ θ)) ^ 2) P := by
  let K : Ω → ℕ := fun ω =>
    hittingBtwn (fun k ω => X.X (clock k) ω) (Ioi z) 0 m ω
  let E : ℝ → Ω → ℝ := fun α ω =>
    Real.exp (α * X.X (clock (K ω)) ω - (clock (K ω) : ℝ) * X.ψ α)
  let B : ℝ := Real.exp ((clock m : ℝ) * max (X.ψ (2 * θ) - 2 * X.ψ θ) 0)
  have hIntθ : Integrable (E θ) P :=
    levy_upper_grid_stopped_exp_integrable X clock hc H hH
      θ hθ z m K (fun _ => rfl)
  have hInt2 : Integrable (E (2 * θ)) P :=
    levy_upper_grid_stopped_exp_integrable X clock hc H hH
      (2 * θ) (by positivity) z m K (fun _ => rfl)
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
  have hnorm : ∀ᵐ ω ∂P, ‖(E θ ω)^2‖ ≤ ‖B * E (2 * θ) ω‖ := by
    apply Filter.Eventually.of_forall
    intro ω
    have hB : 0 ≤ B := Real.exp_nonneg _
    have hE : 0 ≤ E (2 * θ) ω := Real.exp_nonneg _
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (sq_nonneg (E θ ω))]
    rw [abs_of_nonneg (mul_nonneg hB hE)]
    exact hbound ω
  have hSm : AEStronglyMeasurable (fun ω => (E θ ω)^2) P :=
    hIntθ.aestronglyMeasurable.pow 2
  change Integrable (fun ω => (E θ ω)^2) P
  exact (hInt2.const_mul B).mono hSm hnorm
