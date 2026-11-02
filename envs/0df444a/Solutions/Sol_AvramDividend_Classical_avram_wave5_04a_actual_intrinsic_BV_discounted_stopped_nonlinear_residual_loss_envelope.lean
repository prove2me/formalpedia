-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_intrinsic_BV_discounted_stopped_nonlinear_residual_loss_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:46:36.816009+00:00
-- url     : https://prove2.me/submissions/729400e7-a42c-4a75-b339-9b43876d2d14

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_intrinsic_BV_stopped_nonlinear_downward_residual_uniform_variation_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The genuine original-source downward residual contributes a bounded
nonpositive discounted correction along every stopped source grid.
The one-sided Lipschitz hypothesis is the local derivative bound that
Chat03 can establish for its C¹ verification function. -/
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
      ∀ (q : ℝ) (hq : 0 ≤ q)
        (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω),
        0 ≤ (Finset.range n).sum (fun i =>
          Real.exp (-q * (u i : ℝ)) *
            (w (riskProcess X x D (u i) ω) -
              w (riskProcess X x D (u i) ω -
                (R (u (i + 1)) - R (u i))))) ∧
        (Finset.range n).sum (fun i =>
          Real.exp (-q * (u i : ℝ)) *
            (w (riskProcess X x D (u i) ω) -
              w (riskProcess X x D (u i) ω -
                (R (u (i + 1)) - R (u i))))) ≤
          M * (R (τ ω) - R (u 0)) := by
  filter_upwards
    [avram_wave5_04a_actual_intrinsic_BV_stopped_nonlinear_downward_residual_uniform_variation_envelope
      X hBV x D w hw M hM hLipDown] with ω hω
  obtain ⟨R, hRdef, hRmono, _hinterval, henv⟩ := hω
  refine ⟨R, hRdef, hRmono, ?_⟩
  intro q hq τ u hu n hstop
  have hweights (i : ℕ) :
      0 ≤ Real.exp (-q * (u i : ℝ)) ∧
      Real.exp (-q * (u i : ℝ)) ≤ (1 : ℝ) := by
    constructor
    · exact le_of_lt (Real.exp_pos _)
    · have htime : 0 ≤ (u i : ℝ) := (u i).property
      have harg : -q * (u i : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) htime
      calc
        Real.exp (-q * (u i : ℝ)) ≤ Real.exp 0 := Real.exp_le_exp.mpr harg
        _ = 1 := Real.exp_zero
  simpa [one_mul] using
    (henv τ u hu n hstop
      (fun i => Real.exp (-q * (u i : ℝ))) 1 (by norm_num) hweights)
