-- Prove2me | solution 1 for AvramDividend.Classical.discounted_controlled_risk_grid_first_ruin_le_exp_initial
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:22:40.496987+00:00
-- url     : https://prove2.me/submissions/bd3b4fb7-ba01-46c2-97f7-56841726ce10

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_discounted_controlled_risk_grid_first_ruin_stopped_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {𝓖 : Filtration ℕ mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (h𝓖 : ∀ n : ℕ, 𝓖 n = 𝓕 (n : ℝ≥0))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q)
    (N : ℕ) :
    (∫ ω, stoppedValue
      (fun n : ℕ => fun ω =>
        Real.exp (θ * riskProcess X x D (n : ℝ≥0) ω -
          ((n : ℝ≥0) : ℝ) * q))
      (fun ω => ((hittingBtwn
        (fun n : ℕ => fun ω => riskProcess X x D (n : ℝ≥0) ω)
        (Iio (0 : ℝ)) 0 N ω : ℕ) : WithTop ℕ)) ω ∂P) ≤
      Real.exp (θ * x) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have h0 (ω : Ω) : riskProcess X x D 0 ω = x := by
    unfold riskProcess
    rw [X.X_zero ω, hD.1 ω]
    ring
  have hMean :
      (∫ ω, Real.exp (θ * riskProcess X x D 0 ω) ∂P) =
        Real.exp (θ * x) := by
    simp_rw [h0]
    simp
  have hBound :=
    discounted_controlled_risk_grid_first_ruin_stopped_bound
      X h𝓖 x D hD θ q hθ hψ N
  exact hBound.trans_eq hMean
