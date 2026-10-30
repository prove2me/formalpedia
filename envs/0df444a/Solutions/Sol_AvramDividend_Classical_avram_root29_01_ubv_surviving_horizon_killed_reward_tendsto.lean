-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_ubv_surviving_horizon_killed_reward_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:34:54.190086+00:00
-- url     : https://prove2.me/submissions/86537b7b-0aa8-4973-b0d0-c37358c95259

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_raw_ceiling_grid_scale_tendsto_all_paths
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_lower_clock_strict_preclock_closed_survival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- For the true UBV original-Lévy process, lower survival through the cap
forces every continuously killed grid history to survive; the reward converges
to the genuine clipped first-exit scale reward, even when no exit occurs. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (T : ℝ≥0) (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (nhds 0)) (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - (a-x))
        ((-x) - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η)
    (hBefore : (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω) :
    Tendsto (fun n =>
      ({η : Ω | ∀ s : ℝ≥0,
        s ≤ min ((K n η : ℝ≥0) * mesh n) T → 0 ≤ x + X.X s η}).indicator
          (fun η => Real.exp (-(q * ((min
            ((K n η : ℝ≥0) * mesh n) T) : ℝ))) *
          W (x + X.X (min ((K n η : ℝ≥0) * mesh n) T) η)) ω)
      atTop
      (nhds (if min (twoSidedExitUpTime X (a-x) ω)
            (twoSidedExitDownTime X (-x) ω) < ⊤ then
        Real.exp (-(q * ((min
          (min (twoSidedExitUpTime X (a-x) ω)
            (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
          W (x + X.X (min
            (min (twoSidedExitUpTime X (a-x) ω)
              (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
      else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω))) := by
  have hRaw := avram_root29_01_ubv_raw_ceiling_grid_scale_tendsto_all_paths
    X hnbv q hq W hW a x ha hx0 hxa ω T mesh hmesh hpos K hK
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
      (nhds (if min (twoSidedExitUpTime X (a-x) ω)
            (twoSidedExitDownTime X (-x) ω) < ⊤ then
        Real.exp (-(q * ((min
          (min (twoSidedExitUpTime X (a-x) ω)
            (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
          W (x + X.X (min
            (min (twoSidedExitUpTime X (a-x) ω)
              (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
      else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω))) := by
    simpa only [R] using hRaw
  exact hRaw'.congr' hEq
