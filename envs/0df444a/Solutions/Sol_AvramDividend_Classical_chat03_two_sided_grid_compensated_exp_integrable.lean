-- Prove2me | solution 1 for AvramDividend.Classical.chat03_two_sided_grid_compensated_exp_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T17:30:10.569524+00:00
-- url     : https://prove2.me/submissions/affaa28f-a71b-4554-b38e-d9011b441ee0

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_chat03_martingale_sampled_filtration_reindex_corrected

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Bounded strict two-sided grid exit preserves integrability of the exact
Laplace-compensated exponential. No continuous-time stopping time is needed.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (θ : ℝ) (hθ : 0 ≤ θ) (lower upper : ℝ) (m : ℕ)
    (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Set.Ioi (0 : ℝ)) 0 m ω) :
    Integrable (fun ω => Real.exp
      (θ * X.X (clock (K ω)) ω -
        ((clock (K ω)) : ℝ) * X.ψ θ)) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Z : ℕ → Ω → ℝ := fun k ω => X.X (clock k) ω
  let M : ℕ → Ω → ℝ := fun k ω =>
    Real.exp (θ * X.X (clock k) ω - ((clock k) : ℝ) * X.ψ θ)
  let Y : ℕ → Ω → ℝ := fun k ω =>
    max (Z k ω - upper) (lower - Z k ω)
  have hZ : Adapted H Z := by
    intro k
    change Measurable[H k] (X.X (clock k))
    rw [hH k]
    exact X.adapted (clock k)
  have hY : Adapted H Y := by
    intro k
    change Measurable[H k]
      (fun ω => max (Z k ω - upper) (lower - Z k ω))
    exact ((hZ k).sub measurable_const).max
      (measurable_const.sub (hZ k))
  have hM : Martingale M H P :=
    chat03_martingale_sampled_filtration_reindex_corrected
      (fun t ω => Real.exp
        (θ * X.X t ω - (t : ℝ) * X.ψ θ))
      (levy_compensated_exponential_martingale X θ hθ) clock hc H hH
  let τ : Ω → ℕ∞ := fun ω => (K ω : ℕ∞)
  have hτdef :
      τ = (fun ω =>
        ((hittingBtwn Y (Set.Ioi (0 : ℝ)) 0 m ω : ℕ) : ℕ∞)) := by
    funext ω
    change ((K ω : ℕ) : ℕ∞) =
      ((hittingBtwn Y (Set.Ioi (0 : ℝ)) 0 m ω : ℕ) : ℕ∞)
    exact congrArg (fun k : ℕ => (k : ℕ∞)) (hK ω)
  have hτ : IsStoppingTime H τ := by
    rw [hτdef]
    exact hY.isStoppingTime_hittingBtwn measurableSet_Ioi
  have hbound : ∀ ω, τ ω ≤ m := by
    intro ω
    change ((K ω : ℕ) : ℕ∞) ≤ (m : ℕ∞)
    rw [hK ω]
    exact_mod_cast (hittingBtwn_le (u := Y) (s := Set.Ioi (0 : ℝ))
      (n := 0) (m := m) ω)
  have hMint : ∀ k, Integrable (M k) P :=
    fun k => hM.integrable k
  have hInt : Integrable (stoppedValue M τ) P :=
    integrable_stoppedValue ℕ hτ hMint hbound
  have heq : stoppedValue M τ = fun ω => M (K ω) ω := by
    funext ω
    simp [stoppedValue, τ]
  rw [heq] at hInt
  exact hInt