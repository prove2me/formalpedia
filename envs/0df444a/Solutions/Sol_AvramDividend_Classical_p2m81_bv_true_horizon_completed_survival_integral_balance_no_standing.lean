-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_true_horizon_completed_survival_integral_balance_no_standing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T02:01:37.474801+00:00
-- url     : https://prove2.me/submissions/7beb4580-99c5-49fc-b77c-4e6eb060588b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_genuine_finite_horizon_killed_expectation_no_standing
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_horizon_killed_reward_two_way_split
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Standing-free BV completed-upper plus surviving-horizon reward integrates to Wq(x),
via the root-based killed expectation and the standing-free two-way split. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) :
    (let S : Ω → ℝ := fun ω =>
      let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
      let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
      (if U < D ∧ U.toNNReal ≤ T then
        Real.exp (-(q * (U.toNNReal : ℝ))) * W (x + X.X U.toNNReal ω)
      else 0) +
      (if (T : ℝ≥0∞) < U ∧ (T : ℝ≥0∞) < D then
        Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)
      else 0);
    Integrable S P ∧ (∫ ω, S ω ∂P) = W x) := by
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
  let Z : Ω → ℝ := fun ω =>
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
      W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω)
  let S : Ω → ℝ := fun ω =>
    let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
    let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
    (if U < D ∧ U.toNNReal ≤ T then
      Real.exp (-(q * (U.toNNReal : ℝ))) * W (x + X.X U.toNNReal ω)
    else 0) +
    (if (T : ℝ≥0∞) < U ∧ (T : ℝ≥0∞) < D then
      Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)
    else 0)
  have hZS : Z = S := by
    funext ω
    exact avram_ws01b_actual_horizon_killed_reward_two_way_split
      X q W a x ha hxa T ω
  have hZ := p2m81_bv_genuine_finite_horizon_killed_expectation_no_standing
    X q φ hq hφ hroot W hW hBV a x ha hx0 hxa T mesh hmesh hpos K hK
  change Integrable Z P ∧ (∫ ω, Z ω ∂P) = W x at hZ
  rw [hZS] at hZ
  exact hZ
