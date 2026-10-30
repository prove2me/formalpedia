-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_bv_lower_first_killed_grid_reward_tendsto_zero_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T12:19:57.490998+00:00
-- url     : https://prove2.me/submissions/52c9db5b-2c48-4771-8a06-c241ab44eef6

import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_lower_first_capped_terminal_scale_zero_ae
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_ceiling_grid_scale_tendsto_ae_all_paths

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- Killed first-grid BV q-scale rewards vanish on actual lower-first trajectories. -/
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
      twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a-x) ω →
      (twoSidedExitDownTime X (-x) ω).toNNReal ≤ T →
      Tendsto (fun n =>
        ({η : Ω | ∀ s : ℝ≥0,
          s ≤ min ((K n η : ℝ≥0) * mesh n) T → 0 ≤ x + X.X s η}).indicator
          (fun η => Real.exp (-(q * ((min
              ((K n η : ℝ≥0) * mesh n) T) : ℝ))) *
            W (x + X.X (min ((K n η : ℝ≥0) * mesh n) T) η)) ω)
        atTop (𝓝 0) := by
  have hRaw := avram_ws01b_bv_ceiling_grid_scale_tendsto_ae_all_paths
    X hX q hq W hW hBV a x ha hx0 hxa T mesh hmesh hpos K hK
  have hZero := avram_ws01b_bv_lower_first_capped_terminal_scale_zero_ae
    X hX q hq W hW hBV a x ha hx0 hxa T
  filter_upwards [hRaw, hZero] with ω hRawω hZeroω
  intro hDown hCap
  let R : ℕ → Ω → ℝ := fun n η =>
    Real.exp (-(q * ((min ((K n η : ℝ≥0) * mesh n) T) : ℝ))) *
      W (x + X.X (min ((K n η : ℝ≥0) * mesh n) T) η)
  let S : ℕ → Set Ω := fun n => {η : Ω | ∀ s : ℝ≥0,
    s ≤ min ((K n η : ℝ≥0) * mesh n) T → 0 ≤ x + X.X s η}
  have hfinite : min (twoSidedExitUpTime X (a-x) ω)
      (twoSidedExitDownTime X (-x) ω) < ⊤ :=
    lt_of_le_of_lt (min_le_right _ _) (lt_of_lt_of_le hDown le_top)
  have hraw0 : Tendsto (fun n => R n ω) atTop (𝓝 0) := by
    simpa only [R, if_pos hfinite, hZeroω hDown hCap] using hRawω
  have hRpos (n : ℕ) : 0 ≤ R n ω := by
    dsimp only [R]
    apply mul_nonneg (Real.exp_nonneg _)
    by_cases hy : 0 ≤ x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω
    · exact hW.2.1 _ hy
    · simpa only [hW.1 _ (lt_of_not_ge hy)] using (le_refl (0 : ℝ))
  have hLow : ∀ n, 0 ≤ (S n).indicator (R n) ω := by
    intro n
    by_cases hs : ω ∈ S n
    · simpa only [Set.indicator_of_mem hs] using hRpos n
    · simp only [Set.indicator_of_notMem hs, le_refl]
  have hUpper : ∀ n, (S n).indicator (R n) ω ≤ R n ω := by
    intro n
    by_cases hs : ω ∈ S n
    · simp only [Set.indicator_of_mem hs, le_refl]
    · simpa only [Set.indicator_of_notMem hs] using hRpos n
  exact Filter.Tendsto.squeeze tendsto_const_nhds hraw0 hLow hUpper
