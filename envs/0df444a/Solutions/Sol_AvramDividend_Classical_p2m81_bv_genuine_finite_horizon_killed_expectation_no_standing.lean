-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_genuine_finite_horizon_killed_expectation_no_standing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T04:24:21.988466+00:00
-- url     : https://prove2.me/submissions/8441e54f-2a7f-43da-9e2c-b7086fd361d4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_masked_capped_grid_integral_convergence
import Theorems.Thm_AvramDividend_Classical_chat03_clipped_grid_clock_bounded
import Theorems.Thm_AvramDividend_Classical_chat03_monotone_clock_reindexed_filtration
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_clipped_hitting_congr
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_actual_clipped_ceiling_grid_killed_ost_eq_nat_no_standing
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_full_killed_ceiling_grid_reward_tendsto_ae_no_standing_public
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_root_doubling_laplace_point_no_standing_public
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_root_scale_pos_no_standing_public

open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0)) (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - (a-x))
        ((-x) - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η)
     :
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
  letI : IsProbabilityMeasure P := X.isProbability
  let clock : ℕ → ℕ → ℝ≥0 := fun n k => min ((k : ℝ≥0) * mesh n) T
  have hc (n : ℕ) : Monotone (clock n) := (chat03_clipped_grid_clock_bounded T (mesh n)).1
  have hc0 (n : ℕ) : clock n 0 = 0 := by simp [clock]
  let H : ℕ → Filtration ℕ mΩ := fun n => Classical.choose (chat03_monotone_clock_reindexed_filtration 𝓕 (clock n) (hc n))
  have hH (n k : ℕ) : H n k = 𝓕 (clock n k) := Classical.choose_spec (chat03_monotone_clock_reindexed_filtration 𝓕 (clock n) (hc n)) k
  have hKc (n : ℕ) (η : Ω) : K n η = hittingBtwn (fun (k : ℕ) ξ => max (X.X (clock n k) ξ - (a-x)) ((-x) - X.X (clock n k) ξ)) (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η := by
    rw [hK n η]; exact chat03_actual_ceiling_capped_grid_clipped_hitting_congr X (-x) (a-x) T (mesh n) (hpos n) η
  let S : ℕ → Set Ω := fun n => {η : Ω | ∀ s : ℝ≥0, s ≤ clock n (K n η) → 0 ≤ x + X.X s η}
  let Y : ℕ → Ω → ℝ := fun n η => (S n).indicator (fun ξ => Real.exp (-(q * (clock n (K n ξ) : ℝ))) * W (x + X.X (clock n (K n ξ)) ξ)) η
  let Z : Ω → ℝ := fun ω => if (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω then (if min (twoSidedExitUpTime X (a-x) ω) (twoSidedExitDownTime X (-x) ω) < ⊤ then Real.exp (-(q * ((min (min (twoSidedExitUpTime X (a-x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) * W (x + X.X (min (min (twoSidedExitUpTime X (a-x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω) else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)) else (if twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a-x) ω then 0 else Real.exp (-(q * ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) * W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω))
  change Integrable Z P ∧ (∫ ω, Z ω ∂P) = W x
  have hYi (n : ℕ) : Integrable (Y n) P := by
    have hE : (∫ ω, Y n ω ∂P) = W x := by simpa only [Y, S, clock, NNReal.coe_min, NNReal.coe_mul] using (p2m81_bv_actual_clipped_ceiling_grid_killed_ost_eq_nat_no_standing X q φ hq hφ hroot W hW hBV x hx0 a T (mesh n) (hpos n) (K n) (hK n))
    by_contra hn; have hzero : (∫ ω, Y n ω ∂P) = 0 := integral_undef hn; rw [hE] at hzero
    exact (ne_of_gt (p2m81_bv_root_scale_pos_no_standing_public X q φ hq hφ hroot W hW hBV x hx0)) hzero
  have hY0 (n : ℕ) (ω : Ω) : 0 ≤ Y n ω := by
    by_cases h : ω ∈ S n
    · have hr : 0 ≤ x + X.X (clock n (K n ω)) ω := h (clock n (K n ω)) le_rfl
      simpa only [Y, Set.indicator_of_mem h] using (mul_nonneg (Real.exp_nonneg _) (hW.2.1 _ hr))
    · simp only [Y, Set.indicator_of_notMem h, le_refl]
  have hcv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω)) := by simpa only [Y, S, clock, Z, NNReal.coe_min, NNReal.coe_mul] using (p2m81_bv_full_killed_ceiling_grid_reward_tendsto_ae_no_standing_public X q φ hq hφ hroot W hW hBV a x ha hx0 hxa T mesh hmesh hpos K hK)
  have hBound (n : ℕ) : clock n (Nat.ceil (T / mesh n)) ≤ T := (chat03_clipped_grid_clock_bounded T (mesh n)).2.2 _
  have hlim := avram_ws01b_actual_masked_capped_grid_integral_convergence X q (le_of_lt hq) W hW (2*φ) x (by positivity : 0 ≤ 2*φ) (p2m81_bv_root_doubling_laplace_point_no_standing_public X q φ hq hφ hroot) clock hc hc0 H hH (-x) (a-x) (fun n => Nat.ceil (T / mesh n)) K hKc T hBound S Y (fun n ω => rfl) hYi hY0 Z hcv
  have hEq (n : ℕ) : (∫ ω, Y n ω ∂P) = W x := by simpa only [Y, S, clock, NNReal.coe_min, NNReal.coe_mul] using (p2m81_bv_actual_clipped_ceiling_grid_killed_ost_eq_nat_no_standing X q φ hq hφ hroot W hW hBV x hx0 a T (mesh n) (hpos n) (K n) (hK n))
  refine ⟨hlim.1, ?_⟩
  have hConst : (fun n : ℕ => ∫ ω, Y n ω ∂P) = (fun _ : ℕ => W x) := funext hEq
  rw [hConst] at hlim; exact tendsto_nhds_unique hlim.2 tendsto_const_nhds
