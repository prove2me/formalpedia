-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_bv_upper_first_killed_grid_reward_tendsto_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T12:31:42.89817+00:00
-- url     : https://prove2.me/submissions/63ba9c05-7e69-4605-860e-76b0bc9e3144

import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_upper_first_ceiling_grid_survival_eventually
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_finite_two_sided_min_isGLB
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_ceiling_grid_scale_tendsto_ae_all_paths

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- On true upper-first paths, the history-killed first-grid reward converges to the source exit payoff. -/
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
      twoSidedExitUpTime X (a-x) ω < twoSidedExitDownTime X (-x) ω →
      (twoSidedExitUpTime X (a-x) ω).toNNReal < T →
      Tendsto (fun n =>
        ({η : Ω | ∀ s : ℝ≥0,
          s ≤ min ((K n η : ℝ≥0) * mesh n) T → 0 ≤ x + X.X s η}).indicator
          (fun η => Real.exp (-(q * ((min ((K n η : ℝ≥0) * mesh n) T) : ℝ))) *
            W (x + X.X (min ((K n η : ℝ≥0) * mesh n) T) η)) ω)
        atTop (𝓝 (Real.exp (-(q * ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
          W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω))) := by
  have hRaw := avram_ws01b_bv_ceiling_grid_scale_tendsto_ae_all_paths
    X hX q hq W hW hBV a x ha hx0 hxa T mesh hmesh hpos K hK
  filter_upwards [hRaw] with ω hRawω
  intro hUp hBefore
  let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
  let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
  have hFinU : U < ⊤ := lt_of_lt_of_le hUp le_top
  have hMin : min U D = U := min_eq_left hUp.le
  have hFin : min U D < ⊤ := by simpa only [hMin] using hFinU
  have hGLB := avram_ws01b_finite_two_sided_min_isGLB
    X ω (-x) (a-x) hFin
  have hClockEq : ((min U D).toNNReal : ℝ≥0∞) = U := by
    simpa only [hMin] using (ENNReal.coe_toNNReal (ne_of_lt hFinU))
  have hBefore' : (min U D).toNNReal < T := by
    simpa only [hMin] using hBefore
  have hSurv := avram_ws01b_actual_upper_first_ceiling_grid_survival_eventually
    X ω a x (min U D).toNNReal T hGLB hClockEq hUp
      hBefore' mesh hmesh hpos K hK
  let R : ℕ → Ω → ℝ := fun n η =>
    Real.exp (-(q * ((min ((K n η : ℝ≥0) * mesh n) T) : ℝ))) *
      W (x + X.X (min ((K n η : ℝ≥0) * mesh n) T) η)
  let S : ℕ → Set Ω := fun n => {η : Ω | ∀ s : ℝ≥0,
    s ≤ min ((K n η : ℝ≥0) * mesh n) T → 0 ≤ x + X.X s η}
  have hRawLim : Tendsto (fun n => R n ω) atTop
      (𝓝 (Real.exp (-(q * (U.toNNReal : ℝ))) * W (x + X.X U.toNNReal ω))) := by
    have hFin' : min (twoSidedExitUpTime X (a-x) ω)
        (twoSidedExitDownTime X (-x) ω) < ⊤ := hFin
    have hMin' : min (twoSidedExitUpTime X (a-x) ω)
        (twoSidedExitDownTime X (-x) ω) =
        twoSidedExitUpTime X (a-x) ω := hMin
    have hFinSource : twoSidedExitUpTime X (a-x) ω < ⊤ := hFinU
    have hBeforeReal : (U.toNNReal : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast hBefore.le
    have hBeforeSource : ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ) ≤ (T : ℝ) :=
      hBeforeReal
    simpa only [R, hMin', if_pos hFin', if_pos hFinSource,
      min_eq_left hBeforeSource,
      min_eq_left (le_of_lt hBefore)] using hRawω
  have hEq : (fun n => (S n).indicator (R n) ω) =ᶠ[atTop]
      (fun n => R n ω) := by
    filter_upwards [hSurv] with n hn
    have hmem : ω ∈ S n := hn
    exact Set.indicator_of_mem hmem (R n)
  exact hRawLim.congr' hEq.symm
