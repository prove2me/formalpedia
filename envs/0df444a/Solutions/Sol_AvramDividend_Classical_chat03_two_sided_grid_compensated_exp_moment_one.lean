-- Prove2me | solution 1 for AvramDividend.Classical.chat03_two_sided_grid_compensated_exp_moment_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T17:19:44.034891+00:00
-- url     : https://prove2.me/submissions/8e163936-2f25-40a5-8946-cab80e79c64e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_chat03_martingale_sampled_filtration_reindex_corrected
import Theorems.Thm_AvramDividend_Classical_chat03_two_sided_grid_stopped_martingale_identity
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
open AvramDividend.Classical

/-!
Finite grid two-sided exit: exactly unit expectation for the stopped
Laplace-compensated exponential martingale. Proof imports only Proved
children and the precise published Levy process structure.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (θ : ℝ) (hθ : 0 ≤ θ) (lower upper : ℝ) (m : ℕ)
    (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Set.Ioi (0 : ℝ)) 0 m ω) :
    (∫ ω, Real.exp (θ * X.X (clock (K ω)) ω -
      ((clock (K ω)) : ℝ) * X.ψ θ) ∂P) = 1 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Z : ℕ → Ω → ℝ := fun k ω => X.X (clock k) ω
  let M : ℕ → Ω → ℝ := fun k ω =>
    Real.exp (θ * X.X (clock k) ω - ((clock k) : ℝ) * X.ψ θ)
  have hZ : Adapted H Z := by
    intro k
    change Measurable[H k] (X.X (clock k))
    rw [hH k]
    exact X.adapted (clock k)
  have hM : Martingale M H P := by
    exact chat03_martingale_sampled_filtration_reindex_corrected
      (fun t ω => Real.exp
        (θ * X.X t ω - (t : ℝ) * X.ψ θ))
      (levy_compensated_exponential_martingale X θ hθ) clock hc H hH
  have hstop :=
    chat03_two_sided_grid_stopped_martingale_identity
      Z M hZ hM lower upper m
  have hzero : ∀ ω, M 0 ω = 1 := by
    intro ω
    simp [M, hc0, X.X_zero ω]
  have hint : (∫ ω, M 0 ω ∂P) = 1 := by
    simp_rw [hzero]
    simp
  have hmain : (∫ ω, M (K ω) ω ∂P) = 1 := by
    have hp := hstop.trans hint
    simpa only [hK] using hp
  exact hmain