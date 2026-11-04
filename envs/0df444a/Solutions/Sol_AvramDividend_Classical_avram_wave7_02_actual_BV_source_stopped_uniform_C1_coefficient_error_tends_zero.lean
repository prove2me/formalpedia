-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_actual_BV_source_stopped_uniform_C1_coefficient_error_tends_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:04:05.459308+00:00
-- url     : https://prove2.me/submissions/fb7234d6-cebe-4c3b-a7ba-8112948ba1eb

import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_uniform_stopped_coefficient_approximation_error

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Uniform convergence of C¹ coefficient approximations on the exact
original-source monotone BV residual, along arbitrary stopped finite
time partitions. No pure-jump representation or Itô identity is assumed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℕ → ℝ≥0)
        (hu : ∀ k : ℕ, Monotone (u k))
        (n : ℕ → ℕ) (hstart : ∀ k : ℕ, u k 0 = 0)
        (hstop : ∀ k : ℕ, u k (n k) ≤ τ ω)
        (a b : ℕ → ℕ → ℝ) (M : ℕ → ℝ)
        (hM : ∀ k : ℕ, 0 ≤ M k)
        (hMlim : Tendsto M atTop (𝓝 (0 : ℝ)))
        (hab : ∀ k i : ℕ, |a k i - b k i| ≤ M k),
        Tendsto (fun k : ℕ =>
          (Finset.range (n k)).sum (fun i =>
            a k i * (R (u k (i + 1)) - R (u k i))) -
          (Finset.range (n k)).sum (fun i =>
            b k i * (R (u k (i + 1)) - R (u k i))))
          atTop (𝓝 (0 : ℝ)) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_uniform_stopped_coefficient_approximation_error
      X hBV] with ω hω
  obtain ⟨R, hRdef, hRmono, hstab⟩ := hω
  refine ⟨R, hRdef, hRmono, ?_⟩
  intro τ u hu n hstart hstop a b M hM hMlim hab
  let A : ℝ := R (τ ω) - R 0
  have hbound (k : ℕ) :
      |(Finset.range (n k)).sum (fun i =>
          a k i * (R (u k (i + 1)) - R (u k i))) -
        (Finset.range (n k)).sum (fun i =>
          b k i * (R (u k (i + 1)) - R (u k i)))| ≤
        M k * A := by
    have hk := hstab τ (u k) (hu k) (n k) (hstop k)
      (a k) (b k) (M k) (hM k) (hab k)
    simpa [A, hstart k] using hk
  have hlim : Tendsto (fun k : ℕ => M k * A) atTop (𝓝 (0 : ℝ)) := by
    simpa using hMlim.mul_const A
  have hAbs : Tendsto (fun k : ℕ =>
      |(Finset.range (n k)).sum (fun i =>
        a k i * (R (u k (i + 1)) - R (u k i))) -
      (Finset.range (n k)).sum (fun i =>
        b k i * (R (u k (i + 1)) - R (u k i)))|)
      atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun _ => abs_nonneg _) hbound hlim
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (by simpa only [Real.norm_eq_abs] using hAbs)
