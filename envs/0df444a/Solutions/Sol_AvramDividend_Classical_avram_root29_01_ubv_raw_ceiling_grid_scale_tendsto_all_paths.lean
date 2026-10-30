-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_ubv_raw_ceiling_grid_scale_tendsto_all_paths
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:26:35.476407+00:00
-- url     : https://prove2.me/submissions/1b0153cd-2c2e-4b1f-8899-3bdcb001d669

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_scale_tendsto_all_branches
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_finite_two_sided_min_isGLB
import Theorems.Thm_AvramDividend_Classical_chat03_no_grid_exit_when_both_passages_infinite
import Theorems.Thm_AvramDividend_Classical_chat03_noexit_sampled_clock_caps_to_horizon
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- For the original UBV Lévy process, the actual ceiling-capped two-sided
grid q-scale payoff converges on every path, including infinite exit times. -/
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
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η) :
    Tendsto (fun n =>
      Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
        W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω))
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
  have hzero : W 0 = 0 :=
    chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW
  let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
  let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
  by_cases hf : min U D < ⊤
  · have hGLB := avram_ws01b_finite_two_sided_min_isGLB
      X ω (-x) (a-x) hf
    have hRaw := chat03_actual_ceiling_capped_grid_scale_tendsto_all_branches
      X q W hW hzero ω (-x) (a-x) x (min U D).toNNReal T
      hGLB mesh hmesh hpos K hK
    simpa only [U, D, if_pos hf] using hRaw
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
        (fun _ : ℕ => Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)) := by
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
          (nhds (Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω))))
