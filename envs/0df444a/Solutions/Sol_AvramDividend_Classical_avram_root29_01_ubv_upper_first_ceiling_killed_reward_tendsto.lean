-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_ubv_upper_first_ceiling_killed_reward_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:33:15.606905+00:00
-- url     : https://prove2.me/submissions/963dec6b-a3e9-4f0e-a5f5-9153d9e59d65

import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_scale_tendsto_all_branches
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_finite_two_sided_min_isGLB
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_upper_first_ceiling_grid_survival_eventually

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- At an actual UBV upper-first passage before the finite cap, the entire
continuous lower-history survives all sufficiently fine stopped meshes, so
the original-P killed scale reward converges to its strict upper payoff. -/
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
    (hUp : twoSidedExitUpTime X (a-x) ω <
      twoSidedExitDownTime X (-x) ω)
    (hBefore : (twoSidedExitUpTime X (a-x) ω).toNNReal < T) :
    Tendsto (fun n =>
      ({η : Ω | ∀ s : ℝ≥0,
        s ≤ min ((K n η : ℝ≥0) * mesh n) T → 0 ≤ x + X.X s η}).indicator
        (fun η => Real.exp (-(q * ((min
            ((K n η : ℝ≥0) * mesh n) T) : ℝ))) *
          W (x + X.X (min ((K n η : ℝ≥0) * mesh n) T) η)) ω)
      atTop (nhds (Real.exp (-(q *
        ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
        W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω))) := by
  have hzero : W 0 = 0 :=
    chat04_scale_zero_origin_of_unbounded_variation
      X hnbv q hq W hW
  let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
  let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
  have hFinU : U < ⊤ := lt_of_lt_of_le hUp le_top
  have hMin : min U D = U := min_eq_left hUp.le
  have hFin : min U D < ⊤ := by
    simpa only [hMin] using hFinU
  have hGLB := avram_ws01b_finite_two_sided_min_isGLB
    X ω (-x) (a-x) hFin
  have hClockEq : ((min U D).toNNReal : ℝ≥0∞) = U := by
    simpa only [hMin] using (ENNReal.coe_toNNReal (ne_of_lt hFinU))
  have hBefore' : (min U D).toNNReal < T := by
    simpa only [hMin] using hBefore
  have hSurv := avram_ws01b_actual_upper_first_ceiling_grid_survival_eventually
    X ω a x (min U D).toNNReal T hGLB hClockEq hUp
      hBefore' mesh hmesh hpos K hK
  have hRaw := chat03_actual_ceiling_capped_grid_scale_tendsto_all_branches
    X q W hW hzero ω (-x) (a-x) x (min U D).toNNReal T
    hGLB mesh hmesh hpos K hK
  let R : ℕ → Ω → ℝ := fun n η =>
    Real.exp (-(q * ((min ((K n η : ℝ≥0) * mesh n) T) : ℝ))) *
      W (x + X.X (min ((K n η : ℝ≥0) * mesh n) T) η)
  let S : ℕ → Set Ω := fun n => {η : Ω | ∀ s : ℝ≥0,
    s ≤ min ((K n η : ℝ≥0) * mesh n) T → 0 ≤ x + X.X s η}
  have hRawLim : Tendsto (fun n => R n ω) atTop
      (nhds (Real.exp (-(q * (U.toNNReal : ℝ))) *
        W (x + X.X U.toNNReal ω))) := by
    have hT : min (min U D).toNNReal T = U.toNNReal := by
      rw [hMin, min_eq_left hBefore.le]
    have hBeforeReal : (U.toNNReal : ℝ) ≤ (T : ℝ) :=
      NNReal.coe_le_coe.mpr hBefore.le
    have hTimeReal : min (((min U D).toNNReal : ℝ)) (T : ℝ) =
        (U.toNNReal : ℝ) := by
      rw [hMin]
      exact min_eq_left hBeforeReal
    have hRaw' := hRaw
    rw [hT, hTimeReal] at hRaw'
    simpa only [R] using hRaw'
  have hEq : (fun n => (S n).indicator (R n) ω) =ᶠ[atTop]
      (fun n => R n ω) := by
    filter_upwards [hSurv] with n hn
    have hmem : ω ∈ S n := hn
    exact Set.indicator_of_mem hmem (R n)
  exact hRawLim.congr' hEq.symm
