-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_bv_surviving_horizon_killed_grid_scale_tendsto_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T12:23:53.55548+00:00
-- url     : https://prove2.me/submissions/fd9d06eb-92a9-4582-bcfc-73a32673e559

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_lower_clock_strict_preclock_closed_survival
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_ceiling_grid_scale_tendsto_ae_all_paths

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- If genuine lower ruin occurs after the horizon, every capped stopped-grid history survives. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0)) (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - (a-x))
        ((-x) - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η) :
    ∀ᵐ ω ∂P,
      (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω →
      Tendsto (fun n =>
        ({η : Ω | ∀ s : ℝ≥0,
          s ≤ min ((K n η : ℝ≥0) * mesh n) T → 0 ≤ x + X.X s η}).indicator
          (fun η => Real.exp (-(q * ((min ((K n η : ℝ≥0) * mesh n) T) : ℝ))) *
            W (x + X.X (min ((K n η : ℝ≥0) * mesh n) T) η)) ω)
        atTop (𝓝 (if min (twoSidedExitUpTime X (a-x) ω)
              (twoSidedExitDownTime X (-x) ω) < ⊤ then
          Real.exp (-(q * ((min
            (min (twoSidedExitUpTime X (a-x) ω)
              (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
            W (x + X.X (min
              (min (twoSidedExitUpTime X (a-x) ω)
                (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
        else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω))) := by
  have hRaw := avram_ws01b_bv_ceiling_grid_scale_tendsto_ae_all_paths
    X hX q hq W hW hBV a x ha hx0 hxa T mesh hmesh hpos K hK
  filter_upwards [hRaw] with ω hRawω
  intro hBefore
  let R : ℕ → Ω → ℝ := fun n η =>
    Real.exp (-(q * ((min ((K n η : ℝ≥0) * mesh n) T) : ℝ))) *
      W (x + X.X (min ((K n η : ℝ≥0) * mesh n) T) η)
  let S : ℕ → Set Ω := fun n => {η : Ω | ∀ s : ℝ≥0,
    s ≤ min ((K n η : ℝ≥0) * mesh n) T → 0 ≤ x + X.X s η}
  have hSurv (n : ℕ) : ω ∈ S n := by
    intro s hs
    exact avram_ws01b_lower_clock_strict_preclock_closed_survival
      X x ω T hBefore s (hs.trans (min_le_right _ _))
  have hEq : (fun n => R n ω) =ᶠ[atTop]
      (fun n => (S n).indicator (R n) ω) := by
    filter_upwards with n
    exact (Set.indicator_of_mem (hSurv n) (R n)).symm
  have hRaw' : Tendsto (fun n => R n ω) atTop
      (𝓝 (if min (twoSidedExitUpTime X (a-x) ω)
              (twoSidedExitDownTime X (-x) ω) < ⊤ then
          Real.exp (-(q * ((min
            (min (twoSidedExitUpTime X (a-x) ω)
              (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
            W (x + X.X (min
              (min (twoSidedExitUpTime X (a-x) ω)
                (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
        else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω))) := by
    simpa only [R] using hRawω
  exact hRaw'.congr' hEq
