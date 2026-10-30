-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_bv_genuine_finite_horizon_killed_expectation_no_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T13:56:57.98708+00:00
-- url     : https://prove2.me/submissions/3a820a9e-6ae9-4297-85b8-3234882b16fc

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_genuine_finite_horizon_killed_expectation_unconditional

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- True BV finite-horizon killed q-scale payoff has expectation Wq(x), including x=0. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) :
    (let Z : Ω → ℝ := fun ω =>
      if (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω then
        if min (twoSidedExitUpTime X (a-x) ω)
          (twoSidedExitDownTime X (-x) ω) < ⊤ then
          Real.exp (-(q * ((min (min
            (twoSidedExitUpTime X (a-x) ω)
            (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
              W (x + X.X (min (min
                (twoSidedExitUpTime X (a-x) ω)
                (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
        else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)
      else if twoSidedExitDownTime X (-x) ω <
              twoSidedExitUpTime X (a-x) ω then 0
      else Real.exp (-(q * ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
        W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω);
    Integrable Z P ∧ (∫ ω, Z ω ∂P) = W x) := by
  let mesh : ℕ → ℝ≥0 := fun n => ((1 : ℝ≥0) / 2) ^ n
  have hmesh : Tendsto mesh atTop (𝓝 (0 : ℝ≥0)) :=
    NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (1 : ℝ≥0) / 2 < 1)
  have hpos : ∀ n : ℕ, 0 < mesh n := by
    intro n
    dsimp [mesh]
    positivity
  let K : ℕ → Ω → ℕ := fun n η => hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - (a-x))
        ((-x) - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η
  have hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - (a-x))
        ((-x) - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η := by
    intro n η
    rfl
  exact avram_ws01b_bv_genuine_finite_horizon_killed_expectation_unconditional
    X hX q hq W hW hBV a x ha hx0 hxa
      T mesh hmesh hpos K hK
