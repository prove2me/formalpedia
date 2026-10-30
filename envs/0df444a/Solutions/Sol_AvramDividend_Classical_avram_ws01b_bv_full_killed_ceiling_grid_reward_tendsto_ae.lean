-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_bv_full_killed_ceiling_grid_reward_tendsto_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T12:59:32.190258+00:00
-- url     : https://prove2.me/submissions/198486a4-8255-4b51-b207-494815c64b32

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_two_sided_horizon_killed_grid_three_way_cover
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_lower_first_killed_grid_reward_tendsto_zero_ae
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_upper_first_killed_grid_reward_tendsto_ae
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_surviving_horizon_killed_grid_scale_tendsto_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- Actual BV full-history killed grid rewards converge a.e. on every original Lévy path. -/
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
      Tendsto (fun n =>
        ({η : Ω | ∀ s : ℝ≥0,
          s ≤ min ((K n η : ℝ≥0) * mesh n) T → 0 ≤ x + X.X s η}).indicator
          (fun η => Real.exp (-(q * ((min ((K n η : ℝ≥0) * mesh n) T) : ℝ))) *
            W (x + X.X (min ((K n η : ℝ≥0) * mesh n) T) η)) ω)
        atTop (𝓝
          (if (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω then
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
            W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω))) := by
  have hH := avram_ws01b_bv_surviving_horizon_killed_grid_scale_tendsto_ae
    X hX q hq W hW hBV a x ha hx0 hxa T mesh hmesh hpos K hK
  have hL := avram_ws01b_bv_lower_first_killed_grid_reward_tendsto_zero_ae
    X hX q hq W hW hBV a x ha hx0 hxa T mesh hmesh hpos K hK
  have hU := avram_ws01b_bv_upper_first_killed_grid_reward_tendsto_ae
    X hX q hq W hW hBV a x ha hx0 hxa T mesh hmesh hpos K hK
  filter_upwards [hH, hL, hU] with ω hHω hLω hUω
  let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
  let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
  rcases avram_ws01b_actual_two_sided_horizon_killed_grid_three_way_cover
    X a x ha ω T with hT | ⟨hD, hCap⟩ | ⟨hUp, hCap⟩
  · simpa only [if_pos hT] using hHω hT
  · have hDfin : D < ⊤ := lt_of_lt_of_le hD le_top
    have hDleT : D ≤ (T : ℝ≥0∞) := by
      simpa only [ENNReal.coe_toNNReal (ne_of_lt hDfin)] using
        (ENNReal.coe_le_coe.mpr hCap : (D.toNNReal : ℝ≥0∞) ≤ (T : ℝ≥0∞))
    have hNotT : ¬ (T : ℝ≥0∞) < D := not_lt.mpr hDleT
    have hNotT' : ¬ (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω := hNotT
    have hD' : twoSidedExitDownTime X (-x) ω <
        twoSidedExitUpTime X (a-x) ω := hD
    simpa only [if_neg hNotT', if_pos hD'] using hLω hD' hCap
  · by_cases hT : (T : ℝ≥0∞) < D
    · have hT' : (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω := hT
      simpa only [if_pos hT'] using hHω hT'
    · have hNotD : ¬ D < U := not_lt_of_ge hUp.le
      have hNotT' : ¬ (T : ℝ≥0∞) <
          twoSidedExitDownTime X (-x) ω := hT
      have hNotD' : ¬ twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a-x) ω := hNotD
      simpa only [if_neg hNotT', if_neg hNotD'] using hUω hUp hCap
