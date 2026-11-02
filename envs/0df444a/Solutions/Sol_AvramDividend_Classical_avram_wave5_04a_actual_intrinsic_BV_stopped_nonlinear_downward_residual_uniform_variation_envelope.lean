-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_intrinsic_BV_stopped_nonlinear_downward_residual_uniform_variation_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:32:41.022563+00:00
-- url     : https://prove2.me/submissions/3ea80908-1df7-4d2a-ade9-936e4cbc1a03

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Exact nonlinear source remainder increments are nonnegative losses,
and a one-sided Lipschitz bound gives a horizon-uniform BV variation
envelope, without an assumed nonlinear stochastic integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (hw : Monotone w)
    (M : ℝ) (hM : 0 ≤ M)
    (hLipDown : ∀ (y δ : ℝ), 0 ≤ δ →
      w y - w (y - δ) ≤ M * δ) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      (∀ (s t : ℝ≥0), s ≤ t →
        X.X t ω - X.X s ω =
          ((t : ℝ) - (s : ℝ)) * X.drift -
            (∫⁻ p,
              (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
              ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
                (fun u : ℝ≥0 => (u,
                  X.X u ω - Function.leftLim
                    (fun v : ℝ≥0 => X.X v ω) u)))).toReal -
            (R t - R s)) ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
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
  obtain ⟨R, hRdef, hRmono, hinterval⟩ := hω
  refine ⟨R, hRdef, hRmono, hinterval, ?_⟩
  intro τ u hu n hstop a A hA ha
  have hcell (i : ℕ) : 0 ≤ R (u (i + 1)) - R (u i) :=
    sub_nonneg.mpr (hRmono (hu (Nat.le_succ i)))
  have hdown (i : ℕ) :
      0 ≤ w (riskProcess X x D (u i) ω) -
        w (riskProcess X x D (u i) ω -
          (R (u (i + 1)) - R (u i))) := by
    apply sub_nonneg.mpr
    exact hw (sub_le_self _ (hcell i))
  have hsingle (i : ℕ) :
      a i * (w (riskProcess X x D (u i) ω) -
        w (riskProcess X x D (u i) ω -
          (R (u (i + 1)) - R (u i)))) ≤
      (A * M) * (R (u (i + 1)) - R (u i)) := by
    calc
      a i * (w (riskProcess X x D (u i) ω) -
        w (riskProcess X x D (u i) ω -
          (R (u (i + 1)) - R (u i)))) ≤
          a i * (M * (R (u (i + 1)) - R (u i))) :=
            mul_le_mul_of_nonneg_left
              (hLipDown _ _ (hcell i)) (ha i).1
      _ ≤ A * (M * (R (u (i + 1)) - R (u i))) :=
          mul_le_mul_of_nonneg_right (ha i).2
            (mul_nonneg hM (hcell i))
      _ = (A * M) * (R (u (i + 1)) - R (u i)) := by ring
  have hRtel :
      (Finset.range n).sum (fun i => R (u (i + 1)) - R (u i)) =
        R (u n) - R (u 0) :=
    Finset.sum_range_sub (fun i => R (u i)) n
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (ha i).1 (hdown i)
  · calc
      (Finset.range n).sum (fun i =>
        a i * (w (riskProcess X x D (u i) ω) -
          w (riskProcess X x D (u i) ω -
            (R (u (i + 1)) - R (u i))))) ≤
          (Finset.range n).sum (fun i =>
            (A * M) * (R (u (i + 1)) - R (u i))) := by
              apply Finset.sum_le_sum
              intro i hi
              exact hsingle i
      _ = (A * M) * (R (u n) - R (u 0)) := by
          rw [← Finset.mul_sum]
          rw [hRtel]
      _ ≤ (A * M) * (R (τ ω) - R (u 0)) :=
          mul_le_mul_of_nonneg_left
            (sub_le_sub_right (hRmono hstop) (R (u 0)))
            (mul_nonneg hA hM)
