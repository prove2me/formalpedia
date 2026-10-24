-- Prove2me | solution 1 for AvramDividend.Classical.levy_one_sided_capped_grid_upper_exit_discount_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:35:06.570853+00:00
-- url     : https://prove2.me/submissions/534f5ea2-1f36-4d3c-91fe-1734d6c141e4

import Mathlib.Probability.Process.HittingTime
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_hittingBtwn_congr_before_terminal
import Theorems.Thm_AvramDividend_Classical_levy_capped_upper_grid_exp_moment_one
import Theorems.Thm_AvramDividend_Classical_levy_upper_grid_stopped_exp_integrable
import Theorems.Thm_AvramDividend_Classical_levy_upper_grid_discount_integrable
import Theorems.Thm_AvramDividend_Classical_discounted_upper_exit_of_stopped_exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (θ : ℝ) (hθ : 0 ≤ θ) (hψ : 0 ≤ X.ψ θ)
    (upper : ℝ) (m : ℕ)
    (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => X.X (clock k) ω - upper)
      (Ioi (0 : ℝ)) 0 m ω) :
    (∫ ω, {ω : Ω | upper < X.X (clock (K ω)) ω}.indicator
      (fun z => Real.exp (-((clock (K z)) : ℝ) * X.ψ θ)) ω ∂P) ≤
      Real.exp (-θ * upper) := by
  have hK' : ∀ ω : Ω, K ω =
      hittingBtwn (fun k ω => X.X (clock k) ω) (Ioi upper) 0 m ω := by
    intro ω
    rw [hK ω]
    simp [hittingBtwn_def, mem_Ioi, sub_pos]
  have hwhole : Integrable
      (fun ω => Real.exp
        (θ * X.X (clock (K ω)) ω - ((clock (K ω)) : ℝ) * X.ψ θ)) P :=
    levy_upper_grid_stopped_exp_integrable X clock hc H hH θ hθ upper m K hK'
  have hpart : Integrable
      ({ω : Ω | upper < X.X (clock (K ω)) ω}.indicator
        (fun ω => Real.exp (-(((clock (K ω)) : ℝ) * X.ψ θ)))) P := by
    simpa only [neg_mul] using
      (levy_upper_grid_discount_integrable
        X clock H hH upper m K hK' (X.ψ θ) hψ)
  let J : Ω → ℕ := fun ω =>
    hittingBtwn (fun k ω => X.X (clock k) ω) (Ioi upper) 0 m ω
  have hmomentJ : (∫ ω, Real.exp
        (θ * X.X (clock (J ω)) ω - ((clock (J ω)) : ℝ) * X.ψ θ) ∂P) = 1 := by
    simpa only [J] using
      (levy_capped_upper_grid_exp_moment_one
        X clock hc hc0 H hH θ hθ upper m)
  have hmoment : (∫ ω, Real.exp
        (θ * X.X (clock (K ω)) ω - ((clock (K ω)) : ℝ) * X.ψ θ) ∂P) = 1 := by
    calc
      _ = (∫ ω, Real.exp
            (θ * X.X (clock (J ω)) ω - ((clock (J ω)) : ℝ) * X.ψ θ) ∂P) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (by
          intro ω
          dsimp only [J]
          rw [hK' ω])
      _ = 1 := hmomentJ
  simpa only [neg_mul] using
    (discounted_upper_exit_of_stopped_exponential
      P upper θ hθ
      (fun ω => X.X (clock (K ω)) ω)
      (fun ω => ((clock (K ω)) : ℝ) * X.ψ θ)
      {ω : Ω | upper < X.X (clock (K ω)) ω}
      (by intro ω hw; exact le_of_lt hw)
      hwhole hpart (le_of_eq hmoment))
