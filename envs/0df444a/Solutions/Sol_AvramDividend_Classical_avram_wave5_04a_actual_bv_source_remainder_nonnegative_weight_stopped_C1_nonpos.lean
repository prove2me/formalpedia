-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_source_remainder_nonnegative_weight_stopped_C1_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:48:02.668986+00:00
-- url     : https://prove2.me/submissions/92ed0326-5e51-478d-b6b7-44cf566850ac

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_canonical_remainder_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- For the actual bounded-variation source, any nonnegative time weights
preserve the downward sign of the stopped C1 source-residual variation.
The weights may specialise to discount factors; this is not Ito-Meyer. -/
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
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
        (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i),
        (∑ i : Fin n,
          -(a i * deriv w (riskProcess X x D (u i) ω)) *
            (R (u (i + 1)) - R (u i))) ≤ 0 := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_canonical_remainder_monotone X hBV]
    with ω hmono
  let R (t : ℝ≥0) : ℝ :=
    ((t : ℝ) * X.drift - X.X t ω) -
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ t then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal
  refine ⟨R, ?_, hmono, ?_⟩
  · intro t
    rfl
  intro τ u hu n hstop a ha
  apply Finset.sum_nonpos
  intro i hi
  have hincr : 0 ≤ R (u (i + 1)) - R (u i) :=
    sub_nonneg.mpr (hmono (hu (Nat.le_succ (i : ℕ))))
  have hw' : 0 ≤ deriv w (riskProcess X x D (u i) ω) :=
    hw.deriv_nonneg
  have hcoeff : 0 ≤ a i * deriv w (riskProcess X x D (u i) ω) :=
    mul_nonneg (ha i) hw'
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcoeff) hincr
