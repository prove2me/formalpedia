-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_BV_all_Y_physical_grid_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T22:00:08.499228+00:00
-- url     : https://prove2.me/submissions/e4995823-f612-428f-8326-990b78e9bab8

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Every genuine BV Y physical grid has source variation bounded by drift and R. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      ∀ (u : ℕ → ℝ≥0) (n : ℕ),
        (∀ i, i < n → u i ≤ u (i + 1)) →
        (∑ i ∈ Finset.range n,
          |Y (u (i + 1)) - Y (u i)|) ≤
        |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
          (R (u n) - R (u 0)) := by
  filter_upwards [avram_p3_a_bvdrift_original_raw_removed_residual_monotone
    X hBV] with ω hMono
  intro J Y R u n hGrid
  have hR : Monotone R := hMono
  have hStep : ∀ i, i < n →
      |Y (u (i + 1)) - Y (u i)| ≤
        |X.drift| * ((u (i + 1) : ℝ) - (u i : ℝ)) +
          (R (u (i + 1)) - R (u i)) := by
    intro i hi
    have hOrd : (u i : ℝ) ≤ (u (i + 1) : ℝ) := by
      exact_mod_cast hGrid i hi
    have hTime : 0 ≤ (u (i + 1) : ℝ) - (u i : ℝ) :=
      sub_nonneg.mpr hOrd
    have hResidual : 0 ≤ R (u (i + 1)) - R (u i) :=
      sub_nonneg.mpr (hR (hGrid i hi))
    have hIdentity :
        Y (u (i + 1)) - Y (u i) =
          X.drift * ((u (i + 1) : ℝ) - (u i : ℝ)) -
            (R (u (i + 1)) - R (u i)) := by
      dsimp [Y, R]
      ring
    rw [hIdentity]
    calc
      |X.drift * ((u (i + 1) : ℝ) - (u i : ℝ)) -
        (R (u (i + 1)) - R (u i))| ≤
        |X.drift * ((u (i + 1) : ℝ) - (u i : ℝ))| +
          |R (u (i + 1)) - R (u i)| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              (abs_add_le
                (X.drift * ((u (i + 1) : ℝ) - (u i : ℝ)))
                (-(R (u (i + 1)) - R (u i))))
      _ = |X.drift| * ((u (i + 1) : ℝ) - (u i : ℝ)) +
          (R (u (i + 1)) - R (u i)) := by
            rw [abs_mul, abs_of_nonneg hTime,
              abs_of_nonneg hResidual]
  have hTelescope (g : ℕ → ℝ) (m : ℕ) :
      (∑ k ∈ Finset.range m, (g (k + 1) - g k)) = g m - g 0 := by
    induction m with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have hTimeSum :
      (∑ i ∈ Finset.range n, ((u (i + 1) : ℝ) - (u i : ℝ))) =
        (u n : ℝ) - (u 0 : ℝ) :=
    hTelescope (fun k => (u k : ℝ)) n
  have hRSum :
      (∑ i ∈ Finset.range n, (R (u (i + 1)) - R (u i))) =
        R (u n) - R (u 0) :=
    hTelescope (fun k => R (u k)) n
  calc
    (∑ i ∈ Finset.range n,
      |Y (u (i + 1)) - Y (u i)|) ≤
      ∑ i ∈ Finset.range n,
        (|X.drift| * ((u (i + 1) : ℝ) - (u i : ℝ)) +
          (R (u (i + 1)) - R (u i))) := by
            apply Finset.sum_le_sum
            intro i hi
            exact hStep i (Finset.mem_range.mp hi)
    _ = |X.drift| * ((u n : ℝ) - (u 0 : ℝ)) +
          (R (u n) - R (u 0)) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum,
              hTimeSum, hRSum]
