-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_intrinsic_BV_stopped_C1_compact_deterministic_derivative_ceiling_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:19:41.362989+00:00
-- url     : https://prove2.me/submissions/10978918-8f7f-4894-8669-25e45d54ff46

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_deriv_bounded_on_compact_of_contDiff_one
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_intrinsic_BV_stopped_compact_C1_nonlinear_downward_residual_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- A deterministic compact C¹ derivative ceiling suffices for the
stopped nonlinear finite-variation loss of the *original* BV Lévy source.
The source residual is defined by its genuine negative left jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (hw : Monotone w)
    (cap l r : ℝ) (hlr : l < r)
    (hsub : Icc l r ⊆ Ioo 0 cap)
    (hC1 : ContDiffOn ℝ 1 w (Ioo 0 cap)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
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
  obtain ⟨M, hM, hderiv⟩ :=
    deriv_bounded_on_compact_of_contDiff_one w cap l r hlr hsub hC1
  have hdiff : ∀ z ∈ Icc l r, DifferentiableAt ℝ w z := by
    intro z hz
    exact (hC1.contDiffAt (isOpen_Ioo.mem_nhds (hsub hz))).differentiableAt
      (by norm_num)
  refine ⟨M, hM, ?_⟩
  filter_upwards
    [avram_wave5_04a_actual_intrinsic_BV_stopped_compact_C1_nonlinear_downward_residual_envelope
      X hBV x D w hw] with ω hω
  obtain ⟨R, hRdef, hRmono, henv⟩ := hω
  refine ⟨R, hRdef, hRmono, ?_⟩
  intro τ u hu n hstop hcell a A hA ha
  exact henv l r M hlr.le hM hdiff hderiv τ u hu n hstop hcell a A hA ha
