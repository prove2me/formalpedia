-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_canonical_source_remainder_stopped_monotone_w_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:48:57.524424+00:00
-- url     : https://prove2.me/submissions/36892ef1-a66c-488d-8dac-c3fa14e2322d

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_canonical_source_remainder_stopped_C1_nonpos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- For any increasing real verification candidate, the exact actual BV
source remainder contributes nonpositively along every stopped partition;
nonnegativity of its derivative is automatic from monotonicity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw : Monotone w) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (u : ℝ≥0),
            if 0 < u ∧ u ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω),
        (∑ i : Fin n,
          -(deriv w (riskProcess X x D (u i) ω)) *
            (R (u (i + 1)) - R (u i))) ≤ 0 := by
  filter_upwards
    [avram_wave5_04a_actual_bv_canonical_source_remainder_stopped_C1_nonpos
      X hBV x D hD w] with ω hω
  obtain ⟨R, hRdef, hRmono, hsign⟩ := hω
  refine ⟨R, hRdef, hRmono, ?_⟩
  intro τ u hu n hstop
  apply hsign τ u hu n hstop
  intro i
  exact hw.deriv_nonneg
