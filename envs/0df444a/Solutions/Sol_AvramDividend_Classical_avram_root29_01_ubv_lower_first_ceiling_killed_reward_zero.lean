-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_ubv_lower_first_ceiling_killed_reward_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:20:34.331909+00:00
-- url     : https://prove2.me/submissions/94b6b7da-1883-4e81-8848-e8b0134d2684

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_scale_tendsto_all_branches
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_finite_two_sided_min_isGLB
import Theorems.Thm_AvramDividend_Classical_chat04_firstDowncrossing_value_le_threshold
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- At a genuine UBV lower-first passage at or before the cap, the true
continuous-history-killed ceiling-grid scale reward tends to zero, including
boundary creeping where unbounded-variation scale W(0) vanishes. -/
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
    (hDown : twoSidedExitDownTime X (-x) ω <
      twoSidedExitUpTime X (a-x) ω)
    (hCap : (twoSidedExitDownTime X (-x) ω).toNNReal ≤ T) :
    Tendsto (fun n =>
      ({η : Ω | ∀ s : ℝ≥0,
        s ≤ min ((K n η : ℝ≥0) * mesh n) T → 0 ≤ x + X.X s η}).indicator
        (fun η => Real.exp (-(q * ((min
            ((K n η : ℝ≥0) * mesh n) T) : ℝ))) *
          W (x + X.X (min ((K n η : ℝ≥0) * mesh n) T) η)) ω)
      atTop (nhds 0) := by
  have hzero : W 0 = 0 :=
    chat04_scale_zero_origin_of_unbounded_variation X hnbv q hq W hW
  let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
  let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
  have hFinD : D < ⊤ := lt_of_lt_of_le hDown le_top
  have hMin : min U D = D := min_eq_right hDown.le
  have hFin : min U D < ⊤ := by simpa only [hMin] using hFinD
  have hGLB := avram_ws01b_finite_two_sided_min_isGLB
    X ω (-x) (a-x) hFin
  have hd : (D.toNNReal : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) := by
    simpa only [D, twoSidedExitDownTime] using
      (ENNReal.coe_toNNReal (ne_of_lt hFinD))
  have hdown : X.X D.toNNReal ω ≤ -x :=
    chat04_firstDowncrossing_value_le_threshold X (-x) ω D.toNNReal hd
  have hNonpos : x + X.X D.toNNReal ω ≤ 0 := by linarith
  have hEndZero : W (x + X.X D.toNNReal ω) = 0 := by
    rcases eq_or_lt_of_le hNonpos with hEq | hNeg
    · simpa [hEq] using hzero
    · exact hW.1 _ hNeg
  have hRaw := chat03_actual_ceiling_capped_grid_scale_tendsto_all_branches
    X q W hW hzero ω (-x) (a-x) x (min U D).toNNReal T
    hGLB mesh hmesh hpos K hK
  let R : ℕ → Ω → ℝ := fun n η =>
    Real.exp (-(q * ((min ((K n η : ℝ≥0) * mesh n) T) : ℝ))) *
      W (x + X.X (min ((K n η : ℝ≥0) * mesh n) T) η)
  let S : ℕ → Set Ω := fun n => {η : Ω | ∀ s : ℝ≥0,
    s ≤ min ((K n η : ℝ≥0) * mesh n) T → 0 ≤ x + X.X s η}
  have hRaw0 : Tendsto (fun n => R n ω) atTop (nhds 0) := by
    have hT : min (min U D).toNNReal T = D.toNNReal := by
      rw [hMin, min_eq_left hCap]
    simpa only [R, hT, hEndZero, mul_zero] using hRaw
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
  exact Filter.Tendsto.squeeze tendsto_const_nhds hRaw0 hLow hUpper
