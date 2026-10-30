-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_bv_ceiling_grid_scale_expectation_tendsto_of_measurable_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:52:22.402467+00:00
-- url     : https://prove2.me/submissions/f2eaad64-9e34-4f0b-bbe1-fe83846b3b23

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_ceiling_grid_scale_tendsto_ae_all_paths
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_clipped_hitting_congr
import Theorems.Thm_AvramDividend_Classical_chat03_clipped_grid_clock_bounded
import Theorems.Thm_AvramDividend_Classical_chat03_monotone_clock_reindexed_filtration
import Theorems.Thm_AvramDividend_Classical_chat03_capped_grid_scale_expectation_of_ae_convergence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- Original BV ceiling-grid stopped q-scale expectations converge under the exact actual L² domination. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (θ : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0)) (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - (a-x))
        ((-x) - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η)
    (hZ : AEStronglyMeasurable (fun ω =>
      if min (twoSidedExitUpTime X (a-x) ω) (twoSidedExitDownTime X (-x) ω) < ⊤ then
        Real.exp (-(q * ((min (min (twoSidedExitUpTime X (a-x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
          W (x + X.X (min (min (twoSidedExitUpTime X (a-x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
      else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)) P) :
    Integrable (fun ω =>
      if min (twoSidedExitUpTime X (a-x) ω) (twoSidedExitDownTime X (-x) ω) < ⊤ then
        Real.exp (-(q * ((min (min (twoSidedExitUpTime X (a-x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
          W (x + X.X (min (min (twoSidedExitUpTime X (a-x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
      else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)) P ∧
    Tendsto (fun n => ∫ ω,
      Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
        W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω) ∂P)
      atTop (𝓝 (∫ ω, (fun ω =>
      if min (twoSidedExitUpTime X (a-x) ω) (twoSidedExitDownTime X (-x) ω) < ⊤ then
        Real.exp (-(q * ((min (min (twoSidedExitUpTime X (a-x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
          W (x + X.X (min (min (twoSidedExitUpTime X (a-x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
      else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)) ω ∂P)) := by
  let clock : ℕ → ℕ → ℝ≥0 := fun n k => min ((k : ℝ≥0) * mesh n) T
  let Z : Ω → ℝ := fun ω =>
      if min (twoSidedExitUpTime X (a-x) ω) (twoSidedExitDownTime X (-x) ω) < ⊤ then
        Real.exp (-(q * ((min (min (twoSidedExitUpTime X (a-x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
          W (x + X.X (min (min (twoSidedExitUpTime X (a-x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
      else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)
  have hc (n : ℕ) : Monotone (clock n) :=
    (chat03_clipped_grid_clock_bounded T (mesh n)).1
  have hc0 (n : ℕ) : clock n 0 = 0 := by simp [clock]
  classical
  let H : ℕ → Filtration ℕ mΩ := fun n => Classical.choose
    (chat03_monotone_clock_reindexed_filtration 𝓕 (clock n) (hc n))
  have hHc : ∀ n k, H n k = 𝓕 (clock n k) := fun n k =>
    (Classical.choose_spec (chat03_monotone_clock_reindexed_filtration 𝓕 (clock n) (hc n))) k
  have hKc : ∀ n ω, K n ω = hittingBtwn
      (fun k ξ => max (X.X (clock n k) ξ - (a-x)) ((-x) - X.X (clock n k) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) ω := by
    intro n ω
    rw [hK n ω]
    exact chat03_actual_ceiling_capped_grid_clipped_hitting_congr
      X (-x) (a-x) T (mesh n) (hpos n) ω
  have hNm (n : ℕ) : clock n (Nat.ceil (T / mesh n)) ≤ T :=
    (chat03_clipped_grid_clock_bounded T (mesh n)).2.2 _
  have hconv0 := avram_ws01b_bv_ceiling_grid_scale_tendsto_ae_all_paths X
    hX q hq W hW hBV a x ha hx0 hxa T mesh hmesh hpos K hK
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n =>
      Real.exp (-(q * (clock n (K n ω) : ℝ))) *
        W (x + X.X (clock n (K n ω)) ω)) atTop (𝓝 (Z ω)) := by
    filter_upwards [hconv0] with ω hw
    simpa only [clock, Z, NNReal.coe_min, NNReal.coe_mul] using hw
  simpa only [clock, Z, NNReal.coe_min, NNReal.coe_mul] using
    (chat03_capped_grid_scale_expectation_of_ae_convergence
      X q (le_of_lt hq) W hW θ x hθ hψ clock hc hc0 H hHc
      (-x) (a-x) (fun n => Nat.ceil (T / mesh n)) K hKc
      T hNm Z hZ hconv)