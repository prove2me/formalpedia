-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_intrinsic_BV_stopped_compact_C1_nonlinear_downward_residual_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:08:18.336866+00:00
-- url     : https://prove2.me/submissions/9dc1c811-472d-4ea1-ac93-7b8306caec3d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The true original BV source's leftover downward finite-variation
component has a uniform nonlinear stopped-grid loss envelope under only
the C¹ derivative bound on the compact interval visited by each cell.
The source negative marks are the intrinsic original left-jump series;
chronological right dividends are never counted as source marks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (hw : Monotone w) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (l r M : ℝ) (hlr : l ≤ r) (hM : 0 ≤ M)
        (hdiff : ∀ z ∈ Icc l r, DifferentiableAt ℝ w z)
        (hderiv : ∀ z ∈ Icc l r, |deriv w z| ≤ M)
        (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
        (hcell : ∀ i < n,
          riskProcess X x D (u i) ω ∈ Icc l r ∧
          riskProcess X x D (u i) ω -
            (R (u (i + 1)) - R (u i)) ∈ Icc l r)
        (a : ℕ → ℝ) (A : ℝ) (hA : 0 ≤ A)
        (ha : ∀ i, 0 ≤ a i ∧ a i ≤ A),
        0 ≤ (Finset.range n).sum (fun i =>
          a i * (w (riskProcess X x D (u i) ω) -
            w (riskProcess X x D (u i) ω -
              (R (u (i + 1)) - R (u i))))) ∧
        (Finset.range n).sum (fun i =>
          a i * (w (riskProcess X x D (u i) ω) -
            w (riskProcess X x D (u i) ω -
              (R (u (i + 1)) - R (u i))))) ≤
          (A * M) * (R (τ ω) - R (u 0)) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition
      X hBV] with ω hω
  obtain ⟨R, hRdef, hRmono, _hinterval⟩ := hω
  refine ⟨R, hRdef, hRmono, ?_⟩
  intro l r M hlr hM hdiff hderiv τ u hu n hstop hcell a A hA ha
  have hnormBound : ∀ z ∈ Icc l r, ‖deriv w z‖ ≤ M := by
    intro z hz
    simpa only [Real.norm_eq_abs] using hderiv z hz
  have hconvex : Convex ℝ (Icc l r) := convex_Icc l r
  have hdelta (i : ℕ) : 0 ≤ R (u (i + 1)) - R (u i) :=
    sub_nonneg.mpr (hRmono (hu (Nat.le_succ i)))
  have hcellBound (i : ℕ) (hi : i < n) :
      0 ≤ w (riskProcess X x D (u i) ω) -
        w (riskProcess X x D (u i) ω -
          (R (u (i + 1)) - R (u i))) ∧
      w (riskProcess X x D (u i) ω) -
        w (riskProcess X x D (u i) ω -
          (R (u (i + 1)) - R (u i))) ≤
        M * (R (u (i + 1)) - R (u i)) := by
    have hlo := hcell i hi
    have hnorm := Convex.norm_image_sub_le_of_norm_deriv_le
      hdiff hnormBound hconvex hlo.2 hlo.1
    have harg :
        riskProcess X x D (u i) ω -
          (riskProcess X x D (u i) ω -
            (R (u (i + 1)) - R (u i))) =
          R (u (i + 1)) - R (u i) := by ring
    have habs :
        |w (riskProcess X x D (u i) ω) -
          w (riskProcess X x D (u i) ω -
            (R (u (i + 1)) - R (u i)))| ≤
          M * (R (u (i + 1)) - R (u i)) := by
      simpa only [Real.norm_eq_abs, harg, abs_of_nonneg (hdelta i)] using hnorm
    constructor
    · apply sub_nonneg.mpr
      exact hw (sub_le_self _ (hdelta i))
    · exact (le_abs_self _).trans habs
  have hsingle (i : ℕ) (hi : i < n) :
      a i * (w (riskProcess X x D (u i) ω) -
        w (riskProcess X x D (u i) ω -
          (R (u (i + 1)) - R (u i)))) ≤
      (A * M) * (R (u (i + 1)) - R (u i)) := by
    calc
      a i * (w (riskProcess X x D (u i) ω) -
        w (riskProcess X x D (u i) ω -
          (R (u (i + 1)) - R (u i)))) ≤
          a i * (M * (R (u (i + 1)) - R (u i))) :=
            mul_le_mul_of_nonneg_left (hcellBound i hi).2 (ha i).1
      _ ≤ A * (M * (R (u (i + 1)) - R (u i))) :=
        mul_le_mul_of_nonneg_right (ha i).2 (mul_nonneg hM (hdelta i))
      _ = (A * M) * (R (u (i + 1)) - R (u i)) := by ring
  have htel :
      (Finset.range n).sum (fun i => R (u (i + 1)) - R (u i)) =
        R (u n) - R (u 0) :=
    Finset.sum_range_sub (fun i => R (u i)) n
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (ha i).1 (hcellBound i (Finset.mem_range.mp hi)).1
  · calc
      (Finset.range n).sum (fun i =>
        a i * (w (riskProcess X x D (u i) ω) -
          w (riskProcess X x D (u i) ω -
            (R (u (i + 1)) - R (u i))))) ≤
          (Finset.range n).sum (fun i =>
            (A * M) * (R (u (i + 1)) - R (u i))) := by
            apply Finset.sum_le_sum
            intro i hi
            exact hsingle i (Finset.mem_range.mp hi)
      _ = (A * M) * (R (u n) - R (u 0)) := by
          rw [← Finset.mul_sum]
          rw [htel]
      _ ≤ (A * M) * (R (τ ω) - R (u 0)) :=
        mul_le_mul_of_nonneg_left
          (sub_le_sub_right (hRmono hstop) (R (u 0)))
          (mul_nonneg hA hM)
