-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_bv_ceiling_grid_scale_tendsto_ae_all_paths
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:44:13.776558+00:00
-- url     : https://prove2.me/submissions/c64ac192-ef43-4f43-b632-23792e06a0b1

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_finite_exit_ceiling_grid_scale_tendsto_ae
import Theorems.Thm_AvramDividend_Classical_chat03_no_grid_exit_when_both_passages_infinite
import Theorems.Thm_AvramDividend_Classical_chat03_noexit_sampled_clock_caps_to_horizon
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- BV ceiling-capped first-grid q-scale convergence on all original paths, including no exit. -/
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
        Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
          W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω))
        atTop
        (𝓝 (if min (twoSidedExitUpTime X (a-x) ω)
              (twoSidedExitDownTime X (-x) ω) < ⊤ then
          Real.exp (-(q * ((min
            (min (twoSidedExitUpTime X (a-x) ω)
              (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
            W (x + X.X (min
              (min (twoSidedExitUpTime X (a-x) ω)
                (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
        else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω))) := by
  have hFinite := avram_ws01b_bv_finite_exit_ceiling_grid_scale_tendsto_ae
    X hX q hq W hW hBV a x ha hx0 hxa T mesh hmesh hpos K hK
  filter_upwards [hFinite] with ω hω
  let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
  let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
  by_cases hf : min U D < ⊤
  · dsimp only [U, D] at hf
    simp only [if_pos hf]
    exact hω hf
  · have htop : min U D = ⊤ :=
      le_antisymm le_top (le_of_not_gt hf)
    have hU : U = ⊤ := by
      apply le_antisymm le_top
      simpa only [htop] using (min_le_left U D)
    have hD : D = ⊤ := by
      apply le_antisymm le_top
      simpa only [htop] using (min_le_right U D)
    have hNo := (chat03_no_grid_exit_when_both_passages_infinite
      X ω (-x) (a-x) hU hD).1
    have hc (n : ℕ) :
        min ((K n ω : ℝ≥0) * mesh n) T = T := by
      rw [hK n ω]
      exact chat03_noexit_sampled_clock_caps_to_horizon
        X ω (-x) (a-x) (mesh n) T (Nat.ceil (T / mesh n))
        (chat03_nnreal_grid_ceiling_bracket T (mesh n) (hpos n)).1
        (fun t _ => hNo t)
    have hconst :
        (fun n =>
          Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
            W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω)) =
        (fun _ : ℕ => Real.exp (-(q * (T : ℝ))) *
          W (x + X.X T ω)) := by
      funext n
      have hreal :
          min (((K n ω : ℝ≥0) : ℝ) * (mesh n : ℝ)) (T : ℝ) =
            (T : ℝ) := by
        have heq := congrArg (fun z : ℝ≥0 => (z : ℝ)) (hc n)
        simpa only [NNReal.coe_min, NNReal.coe_mul] using heq
      rw [hc n, hreal]
    dsimp only [U, D] at hf
    simpa only [if_neg hf, hconst] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => Real.exp (-(q * (T : ℝ))) *
          W (x + X.X T ω)) atTop
          (𝓝 (Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω))))
